import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0011
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0019
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.Bundle0013
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.CountData
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityFormula
import Formalism.UnipotentAdelicQuotients.SWXSDefs
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicBoxLatticeCountRatio
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Pack

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def intSub {d M : ℕ} (b : Module.Basis (Fin d) F E) {Λ : Type} [AddCommGroup Λ]
    (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) : AddSubgroup Λ where
  carrier := {l | ∀ v, (fun a i => (N : Fv F v ⊗[F] E) * projV v (projFin (e l)) a i) ∈ latV b v}
  zero_mem' := by
    intro v a i k
    simp [projV, projFin]
  add_mem' := by
    intro x y hx hy v a i k
    have h := add_mem (hx v a i k) (hy v a i k)
    simpa [projV, projFin, mul_add, map_add] using h
  neg_mem' := by
    intro x hx v a i k
    have h := neg_mem (hx v a i k)
    simpa [projV, projFin, mul_neg, map_neg] using h

def coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E) :
    (Fin 1 → Fin M → AF F ⊗[F] E) →+ PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ) :=
  AddMonoidHom.mk' (fun X => WithLp.toLp 1 fun p =>
    InfinitePlace.Completion.ringEquivRealOfIsReal (IsTotallyReal.isReal p.2.2.2)
      ((Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X p.1 p.2.1) p.2.2.1 p.2.2.2)) (by
    intro X Y
    ext p
    simp only [projInf, map_add, Pi.add_apply, Finsupp.coe_add, PiLp.add_apply]
    exact map_add _ _ _)

theorem norm_coord (hF : IsTotallyReal F) {d M : ℕ} (b : Module.Basis (Fin d) F E)
    (X : Fin 1 → Fin M → AF F ⊗[F] E) : ‖coord hF b X‖ = sizeTup b (projInf X) := by
  rw [PiLp.norm_eq_of_L1]
  simp only [sizeTup, sizeInf, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ =>
    Finset.sum_congr rfl fun v _ => ?_
  exact (InfinitePlace.Completion.isometry_extensionEmbeddingOfIsReal (IsTotallyReal.isReal v)).norm_map_of_map_zero
    (map_zero _) _

theorem finrank_coord (hF : IsTotallyReal F) (d M : ℕ) :
    Module.finrank ℝ (PiLp 1 (fun _ : Fin 1 × Fin M × Fin d × InfinitePlace F => ℝ)) =
      d * Module.finrank ℚ F * M := by
  have h : Fintype.card (InfinitePlace F) = Module.finrank ℚ F := by
    have h1 := InfinitePlace.card_add_two_mul_card_eq_rank F
    have h2 := InfinitePlace.card_eq_nrRealPlaces_add_nrComplexPlaces F
    simp only [IsTotallyReal.nrComplexPlaces_eq_zero] at h1 h2
    omega
  rw [(WithLp.linearEquiv 1 ℝ _).finrank_eq, Module.finrank_fintype_fun_eq_card]
  simp only [Fintype.card_prod, Fintype.card_fin, h]
  ring

theorem box_packing : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (M : ℕ), ∀ (Λ : Type) [AddCommGroup Λ] (e : Λ →+ (Fin 1 → Fin M → AF F ⊗[F] E)) (N : ℕ) (r R : ℝ), 0 < r → r ≤ R → ∑' l : Λ, (Set.indicator (box b N R) (fun _ => (1 : ℝ≥0∞))) (e l) ≤ ENNReal.ofReal ((5 * R / r) ^ (2 * Module.finrank ℚ F * M)) * ∑' l : Λ, (Set.indicator (box b N r) (fun _ => (1 : ℝ≥0∞))) (e l) := by
  intro F E _ _ _ _ _ σ hσ d b M Λ _ e N r R hr hrR
  obtain ⟨hF, -, h2, -⟩ := hσ
  have hd : d = 2 := by
    rw [← h2, Module.finrank_eq_card_basis b, Fintype.card_fin]
  subst hd
  have key := GlobalTheory.T.lattice_ball_count_ratio_bound (PiLp 1 (fun _ : Fin 1 × Fin M × Fin 2 × InfinitePlace F => ℝ)) (intSub b e N)
    ((coord hF b).comp (e.comp (intSub b e N).subtype)) r R hr hrR
  rw [finrank_coord hF 2 M] at key
  have conv : ∀ t : ℝ, ∑' l : Λ, (Set.indicator (box b N t) (fun _ => (1 : ℝ≥0∞))) (e l) =
      ∑' l : intSub b e N, Set.indicator {l : intSub b e N |
        ‖((coord hF b).comp (e.comp (intSub b e N).subtype)) l‖ ≤ t} (fun _ => (1 : ℝ≥0∞)) l := by
    intro t
    have h := tsum_subtype ((intSub b e N : AddSubgroup Λ) : Set Λ)
      (fun l => Set.indicator {l : Λ | sizeTup b (projInf (e l)) ≤ t} (fun _ => (1 : ℝ≥0∞)) l)
    refine Eq.trans ?_ (Eq.trans h.symm ?_)
    · refine tsum_congr fun l => ?_
      have hb : e l ∈ box b N t ↔ l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ) ∧
          l ∈ {l : Λ | sizeTup b (projInf (e l)) ≤ t} := Iff.rfl
      by_cases hm : e l ∈ box b N t
      · rw [Set.indicator_of_mem hm, Set.indicator_of_mem (hb.1 hm).1, Set.indicator_of_mem (hb.1 hm).2]
      · rw [Set.indicator_of_notMem hm]
        by_cases h1 : l ∈ ((intSub b e N : AddSubgroup Λ) : Set Λ)
        · rw [Set.indicator_of_mem h1, Set.indicator_of_notMem fun h => hm (hb.2 ⟨h1, h⟩)]
        · rw [Set.indicator_of_notMem h1]
    · refine tsum_congr fun l => ?_
      simp [Set.indicator, norm_coord]
  rw [conv R, conv r]
  exact key

end GlobalTheory.CompanionTheory.SW.Pack
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleLocalGlobalProperties
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix RestrictedProduct

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.Glue

section Coord

variable {F E : Type} [Field F] [Field E] [Algebra F E]

theorem repr_map {R R' : Type} [CommRing R] [CommRing R'] [Algebra F R] [Algebra F R']
    (φ : R →ₐ[F] R') {d : ℕ} (b : Module.Basis (Fin d) F E) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) k =
      φ ((Algebra.TensorProduct.basis R b).repr y k) := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    simp [Algebra.TensorProduct.basis_repr_tmul, Algebra.smul_def]
  | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]

variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

def coH {d : ℕ} (b : Module.Basis (Fin d) F E) : (R ⊗[F] E) ≃ₜ (Fin d → R) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  haveI : ContinuousAdd (R ⊗[F] E) := IsModuleTopology.toContinuousAdd R _
  { (Algebra.TensorProduct.basis R b).equivFun.toEquiv with
    continuous_toFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.toLinearMap
    continuous_invFun :=
      IsModuleTopology.continuous_of_linearMap (Algebra.TensorProduct.basis R b).equivFun.symm.toLinearMap }

theorem continuous_repr {d : ℕ} (b : Module.Basis (Fin d) F E) (k : Fin d) :
    Continuous fun y : R ⊗[F] E => (Algebra.TensorProduct.basis R b).repr y k :=
  (continuous_apply k).comp (coH R b).continuous

theorem continuous_map {R' : Type} [CommRing R'] [Algebra F R'] [TopologicalSpace R']
    [IsTopologicalRing R'] (φ : R →ₐ[F] R') (hφ : Continuous φ) {d : ℕ}
    (b : Module.Basis (Fin d) F E) :
    Continuous fun y : R ⊗[F] E => Algebra.TensorProduct.map φ (AlgHom.id F E) y := by
  rw [← (coH R' b).comp_continuous_iff]
  refine continuous_pi fun k => ?_
  have : (fun y : R ⊗[F] E => ((coH R' b) ∘ fun y : R ⊗[F] E =>
      Algebra.TensorProduct.map φ (AlgHom.id F E) y) y k) =
      fun y => φ ((Algebra.TensorProduct.basis R b).repr y k) := by
    funext y
    exact repr_map φ b y k
  rw [this]
  exact hφ.comp (continuous_repr R b k)

end Coord

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

def pV (v : HeightOneSpectrum (𝓞 F)) : AF F →ₐ[F] Fv F v := (evalV F v).comp (sndA F)

theorem continuous_pV (v : HeightOneSpectrum (𝓞 F)) : Continuous (pV (F := F) v) :=
  (RestrictedProduct.continuous_eval v).comp continuous_snd

theorem continuous_fstA : Continuous (fstA F) := continuous_fst

variable {d M n : ℕ} (b : Module.Basis (Fin d) F E)

theorem crd_inf (X : Fin n → Fin M → AF F ⊗[F] E) (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Ainf F) b).repr (projInf X a i) k =
      fstA F ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) :=
  repr_map (fstA F) b (X a i) k

theorem crd_v (v : HeightOneSpectrum (𝓞 F)) (X : Fin n → Fin M → AF F ⊗[F] E)
    (a : Fin n) (i : Fin M) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k =
      pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) := by
  have h1 := repr_map (evalV F v) b (projFin X a i) k
  have h2 := repr_map (sndA F) b (X a i) k
  refine h1.trans ?_
  exact congrArg (evalV F v) h2

include b in

theorem tuple_ext (X Y : Fin n → Fin M → AF F ⊗[F] E) (hinf : projInf X = projInf Y)
    (hv : ∀ v, projV v (projFin X) = projV v (projFin Y)) : X = Y := by
  funext a i
  refine (Algebra.TensorProduct.basis (AF F) b).ext_elem fun k => ?_
  refine Prod.ext ?_ ?_
  · have := crd_inf b X a i k
    rw [hinf, crd_inf b Y a i k] at this
    exact this.symm
  · refine Subtype.ext (funext fun v => ?_)
    have := crd_v b v X a i k
    rw [hv v, crd_v b v Y a i k] at this
    exact this.symm

theorem eventually_lat (X : Fin n → Fin M → AF F ⊗[F] E) :
    ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v := by
  have h : ∀ (a : Fin n) (i : Fin M) (k : Fin d), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      (Algebra.TensorProduct.basis (Fv F v) b).repr (projV v (projFin X) a i) k ∈
        v.adicCompletionIntegers F := by
    intro a i k
    have h0 : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
        pV v ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k) ∈
          v.adicCompletionIntegers F :=
      ((Algebra.TensorProduct.basis (AF F) b).repr (X a i) k).2.2
    exact h0.mono fun v hv => by rwa [crd_v]
  have h' := Filter.eventually_all.2 fun a => Filter.eventually_all.2 fun i =>
    Filter.eventually_all.2 (h a i)
  exact h'

theorem exists_glue (Xinf : Fin n → Fin M → Ainf F ⊗[F] E)
    (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E)
    (h : ∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) :
    ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v := by
  let cf : Fin n → Fin M → Fin d → Af F := fun a i k =>
    ⟨fun v => (Algebra.TensorProduct.basis (Fv F v) b).repr (Xv v a i) k, h.mono fun v hv => hv a i k⟩
  let c : Fin n → Fin M → Fin d → AF F := fun a i k =>
    pairA F ((Algebra.TensorProduct.basis (Ainf F) b).repr (Xinf a i) k) (cf a i k)
  let X : Fin n → Fin M → AF F ⊗[F] E := fun a i => (coH (AF F) b).symm (c a i)
  have hX : ∀ a i k, (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k = c a i k := fun a i k =>
    congrFun ((coH (AF F) b).apply_symm_apply (c a i)) k
  refine ⟨X, ?_, fun v => ?_⟩
  · funext a i
    refine (Algebra.TensorProduct.basis (Ainf F) b).ext_elem fun k => ?_
    rw [crd_inf, hX]
    rfl
  · funext a i
    refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
    rw [crd_v, hX]
    rfl

theorem isCompact_box {D : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v)}
    (hc : ∀ v, IsCompact (D v))
    (hf : ∀ᶠ v in Filter.cofinite, D v ⊆ (v.adicCompletionIntegers F : Set (Fv F v))) :
    IsCompact {x : Af F | ∀ v, x v ∈ D v} := by
  let S : Set (HeightOneSpectrum (𝓞 F)) := {v | D v ⊆ (v.adicCompletionIntegers F : Set (Fv F v))}
  have hS : Filter.cofinite ≤ Filter.principal S := Filter.le_principal_iff.2 hf
  let R := fun v : HeightOneSpectrum (𝓞 F) => v.adicCompletion F
  let A := fun v : HeightOneSpectrum (𝓞 F) =>
    (v.adicCompletionIntegers F : Set (v.adicCompletion F))
  let K : Set (Πʳ v, [R v, A v]_[Filter.principal S]) := {x | ∀ v, x v ∈ D v}
  have hK : IsCompact K := by
    rw [RestrictedProduct.isEmbedding_coe_of_principal.isCompact_iff]
    have e : ((↑) : Πʳ v, [R v, A v]_[Filter.principal S] → ∀ v, R v) '' K = Set.pi Set.univ D := by
      ext g
      constructor
      · rintro ⟨x, hx, rfl⟩ v _
        exact hx v
      · intro hg
        refine ⟨⟨g, ?_⟩, fun v => hg v (Set.mem_univ v), rfl⟩
        rw [Filter.eventually_principal]
        intro v hv
        exact hv (hg v (Set.mem_univ v))
    rw [e]
    exact isCompact_univ_pi hc
  have e : {x : Af F | ∀ v, x v ∈ D v} = RestrictedProduct.inclusion R A hS '' K := by
    ext x
    constructor
    · intro hx
      refine ⟨⟨x, ?_⟩, hx, rfl⟩
      rw [Filter.eventually_principal]
      intro v hv
      exact hv (hx v)
    · rintro ⟨y, hy, rfl⟩ v
      exact hy v
  rw [e]
  exact hK.image (RestrictedProduct.continuous_inclusion hS)

theorem isCompact_glue (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E))
    (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E))
    (hinf : IsCompact Cinf) (hv : ∀ v, IsCompact (Cv v))
    (hlat : ∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) :
    IsCompact {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  haveI : T2Space (Ainf F) := inferInstanceAs (T2Space ((w : InfinitePlace F) → w.Completion))
  haveI : T2Space (Ainf F ⊗[F] E) := (coH (Ainf F) b).isEmbedding.t2Space
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), T2Space (Fv F v ⊗[F] E) := fun v =>
    (coH (Fv F v) b).isEmbedding.t2Space

  let DI : Fin n → Fin M → Fin d → Set (Ainf F) := fun a i k =>
    (fun Y : Fin n → Fin M → Ainf F ⊗[F] E =>
      (Algebra.TensorProduct.basis (Ainf F) b).repr (Y a i) k) '' Cinf
  have hDI : ∀ a i k, IsCompact (DI a i k) := fun a i k =>
    hinf.image ((continuous_repr (Ainf F) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  let DV : Fin n → Fin M → Fin d → ∀ v : HeightOneSpectrum (𝓞 F), Set (Fv F v) := fun a i k v =>
    (fun Y : Fin n → Fin M → Fv F v ⊗[F] E =>
      (Algebra.TensorProduct.basis (Fv F v) b).repr (Y a i) k) '' Cv v
  have hDV : ∀ a i k v, IsCompact (DV a i k v) := fun a i k v =>
    (hv v).image ((continuous_repr (Fv F v) b k).comp
      ((continuous_apply i).comp (continuous_apply a)))
  have hB : ∀ a i k, IsCompact {x : Af F | ∀ v, x v ∈ DV a i k v} := fun a i k =>
    isCompact_box (hDV a i k) (hlat.mono fun v hsub => by
      rintro _ ⟨Y, hY, rfl⟩
      exact hsub hY a i k)

  let Q : Fin n → Fin M → Fin d → Set (AF F) := fun a i k =>
    (DI a i k) ×ˢ {x : Af F | ∀ v, x v ∈ DV a i k v}
  have hQ : ∀ a i k, IsCompact (Q a i k) := fun a i k => (hDI a i k).prod (hB a i k)
  let L : Set (Fin n → Fin M → Fin d → AF F) :=
    Set.pi Set.univ fun a => Set.pi Set.univ fun i => Set.pi Set.univ fun k => Q a i k
  have hL : IsCompact L :=
    isCompact_univ_pi fun a => isCompact_univ_pi fun i => isCompact_univ_pi fun k => hQ a i k
  let g : (Fin n → Fin M → Fin d → AF F) → Fin n → Fin M → AF F ⊗[F] E :=
    fun c a i => (coH (AF F) b).symm (c a i)
  have hg : Continuous g := continuous_pi fun a => continuous_pi fun i =>
    (coH (AF F) b).symm.continuous.comp ((continuous_apply i).comp (continuous_apply a))
  have hcl : IsClosed {X : Fin n → Fin M → AF F ⊗[F] E |
      projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
    have c1 : Continuous (projInf : (Fin n → Fin M → AF F ⊗[F] E) → _) :=
      continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (fstA F) continuous_fstA b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have c2 : ∀ v : HeightOneSpectrum (𝓞 F), Continuous
        (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) := fun v => by
      have e : (fun X : Fin n → Fin M → AF F ⊗[F] E => projV v (projFin X)) =
          fun X a i => Algebra.TensorProduct.map (pV v) (AlgHom.id F E) (X a i) := by
        funext X a i
        refine (Algebra.TensorProduct.basis (Fv F v) b).ext_elem fun k => ?_
        rw [crd_v]
        exact (repr_map (pV v) b (X a i) k).symm
      rw [e]
      exact continuous_pi fun a => continuous_pi fun i =>
        (continuous_map (AF F) (pV v) (continuous_pV v) b).comp
          ((continuous_apply i).comp (continuous_apply a))
    have e : {X : Fin n → Fin M → AF F ⊗[F] E |
        projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} =
        projInf ⁻¹' Cinf ∩ ⋂ v, (fun X => projV v (projFin X)) ⁻¹' Cv v := by
      ext X
      simp
    rw [e]
    exact (hinf.isClosed.preimage c1).inter
      (isClosed_iInter fun v => (hv v).isClosed.preimage (c2 v))
  refine (hL.image hg).of_isClosed_subset hcl ?_
  rintro X ⟨h1, h2⟩
  refine ⟨fun a i k => (Algebra.TensorProduct.basis (AF F) b).repr (X a i) k, ?_, ?_⟩
  · intro a _ i _ k _
    refine ⟨⟨projInf X, h1, crd_inf b X a i k⟩, fun v => ⟨_, h2 v, crd_v b v X a i k⟩⟩
  · funext a i
    exact (coH (AF F) b).symm_apply_apply (X a i)

end Adelic

theorem glue_main : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E) (n M : ℕ), (∀ X Y : Fin n → Fin M → AF F ⊗[F] E, projInf X = projInf Y → (∀ v, projV v (projFin X) = projV v (projFin Y)) → X = Y) ∧ (∀ X : Fin n → Fin M → AF F ⊗[F] E, ∀ᶠ v in Filter.cofinite, projV v (projFin X) ∈ latV b v) ∧ (∀ (Xinf : Fin n → Fin M → Ainf F ⊗[F] E) (Xv : ∀ v : HeightOneSpectrum (𝓞 F), Fin n → Fin M → Fv F v ⊗[F] E), (∀ᶠ v in Filter.cofinite, Xv v ∈ latV b v) → ∃ X : Fin n → Fin M → AF F ⊗[F] E, projInf X = Xinf ∧ ∀ v, projV v (projFin X) = Xv v) ∧ ∀ (Cinf : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (Cv : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)), IsCompact Cinf → (∀ v, IsCompact (Cv v)) → (∀ᶠ v in Filter.cofinite, Cv v ⊆ latV b v) → IsCompact {X : Fin n → Fin M → AF F ⊗[F] E | projInf X ∈ Cinf ∧ ∀ v, projV v (projFin X) ∈ Cv v} := by
  intro F E _ _ _ _ _ σ _ d b n M
  exact ⟨tuple_ext b, eventually_lat b, exists_glue b, isCompact_glue b⟩

end GlobalTheory.CompanionTheory.SW.Glue
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicUnitaryGroupLocallyCompact
section
noncomputable section

namespace GlobalTheory.CompanionTheory.SW.TopH

open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

theorem hform_mulVec {A : Type} [CommRing A] {m : ℕ} (σ : A →+* A) (J g : Matrix (Fin m) (Fin m) A)
    (hg : cT σ g * J * g = J) (x y : Fin m → A) :
    hform σ J (g *ᵥ x) (g *ᵥ y) = hform σ J x y := by
  have key : ∀ x y : Fin m → A, hform σ J x y = (fun i => σ (x i)) ⬝ᵥ (J *ᵥ y) := by
    intro x y
    simp [hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc]
  have hs : (fun i => σ ((g *ᵥ x) i)) = (g.map σ) *ᵥ (fun i => σ (x i)) := by
    funext i
    simp [Matrix.mulVec, dotProduct, map_sum, map_mul]
  rw [key, key, hs]
  conv_lhs => rw [dotProduct_comm, Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, dotProduct_comm]
  congr 1
  change cT σ g *ᵥ (J *ᵥ (g *ᵥ y)) = J *ᵥ y
  rw [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hg]

section

variable {F E : Type} [Field F] [Field E] [Algebra F E]
  (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]

theorem isClosed_HR [IsTopologicalRing (R ⊗[F] E)] [T2Space (R ⊗[F] E)] (σ : E →ₐ[F] E) (hs : Continuous (sigR R σ)) {M : ℕ}
    (J : Matrix (Fin M) (Fin M) E) :
    IsClosed (HR R σ J : Set (GL (Fin M) (R ⊗[F] E))) := by
  have hv : Continuous fun g : GL (Fin M) (R ⊗[F] E) => (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    Units.continuous_val
  have hc : Continuous fun g : GL (Fin M) (R ⊗[F] E) =>
      cT (sigR R σ) (g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * JR R J * (g : Matrix (Fin M) (Fin M) _) := by
    refine ((Continuous.matrix_transpose (Continuous.matrix_map hv hs)).matrix_mul continuous_const).matrix_mul hv
  exact isClosed_eq hc continuous_const

end

theorem topH_props : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R] [LocallyCompactSpace R] [SecondCountableTopology R] [T2Space R], IsTopologicalGroup (HA R σ J) ∧ LocallyCompactSpace (HA R σ J) ∧ SecondCountableTopology (HA R σ J) ∧ T2Space (HA R σ J) ∧ BorelSpace (HA R σ J) ∧ ∀ n : ℕ, (Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) => actW R σ J p.1 p.2) ∧ (∀ X : Fin n → Fin M → R ⊗[F] E, actW R σ J 1 X = X) ∧ (∀ (g h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), actW R σ J (g * h) X = actW R σ J g (actW R σ J h X)) ∧ ∀ (h : HA R σ J) (X : Fin n → Fin M → R ⊗[F] E), gramR R σ J (actW R σ J h X) = gramR R σ J X := by
  intro F E _ _ _ _ _ σ hCM M J _ R _ _ _ _ _ _ _
  obtain ⟨h1, h2, h3, h4, hs, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hCM R
  haveI := h1; haveI := h2; haveI := h3; haveI := h4
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (LocallyCompactSpace (Fin M → Fin M → R ⊗[F] E))
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (SecondCountableTopology (Fin M → Fin M → R ⊗[F] E))
  haveI : T2Space (Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
    inferInstanceAs (T2Space (Fin M → Fin M → R ⊗[F] E))
  haveI : LocallyCompactSpace (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.isOpenEmbedding.locallyCompactSpace
  haveI : SecondCountableTopology (Matrix (Fin M) (Fin M) (R ⊗[F] E))ᵐᵒᵖ :=
    MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : LocallyCompactSpace (GL (Fin M) (R ⊗[F] E)) :=
    Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  haveI : SecondCountableTopology (GL (Fin M) (R ⊗[F] E)) :=
    Units.isEmbedding_embedProduct.isInducing.secondCountableTopology
  have hcl := isClosed_HR R σ hs J
  haveI g1 : IsTopologicalGroup (HR R σ J) := inferInstance
  haveI g2 : LocallyCompactSpace (HR R σ J) := hcl.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI g3 : SecondCountableTopology (HR R σ J) := Topology.IsInducing.subtypeVal.secondCountableTopology
  haveI g4 : T2Space (HR R σ J) := inferInstance
  refine ⟨g1, g2, g3, g4, ⟨rfl⟩, fun n => ⟨?_, ?_, ?_, ?_⟩⟩
  · have hm : Continuous fun p : HA R σ J × (Fin n → Fin M → R ⊗[F] E) =>
        ((HA.mat R σ J p.1 : GL (Fin M) (R ⊗[F] E)) : Matrix (Fin M) (Fin M) (R ⊗[F] E)) :=
      Units.continuous_val.comp (continuous_subtype_val.comp continuous_fst)
    exact continuous_pi fun a => hm.matrix_mulVec ((continuous_apply a).comp continuous_snd)
  · intro X
    funext a
    exact Matrix.one_mulVec (X a)
  · intro g h X
    funext a
    change ((HA.mat R σ J g : Matrix (Fin M) (Fin M) (R ⊗[F] E)) * (HA.mat R σ J h : Matrix (Fin M) (Fin M) _)) *ᵥ X a = _
    exact (Matrix.mulVec_mulVec _ _ _).symm
  · intro h X
    funext a b
    exact hform_mulVec (sigR R σ) (JR R J) _ h.2 (X a) (X b)

end GlobalTheory.CompanionTheory.SW.TopH
end
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.ArithmeticUnitaryGroupDiscreteStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.arithmetic_unitary_group_discrete : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → Countable (HFinIn (AF F) σ J) ∧ ∃ U ∈ 𝓝 (1 : HA (AF F) σ J), ∀ h ∈ U, HA.mat (AF F) σ J h ∈ HFin (AF F) σ J → h = 1 := by
  first | exact @GlobalTheory.CompanionTheory.SW.rational_countable_discrete | exact GlobalTheory.CompanionTheory.SW.rational_countable_discrete | (intros; apply GlobalTheory.CompanionTheory.SW.rational_countable_discrete <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneDetHermitianGramStatement
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.block_one_det_hermitian_gram : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E) (t : F), (blockOne (algebraMap F E t) J).det = algebraMap F E t * J.det ∧ ((∀ a b, σ (J b a) = J a b) → ∀ a b, σ (blockOne (algebraMap F E t) J b a) = blockOne (algebraMap F E t) J a b) ∧ (∀ (n : ℕ) (X : Fin n → Fin M → E), gramE σ (blockOne (algebraMap F E t) J) (consTup X) = blockOne (algebraMap F E t) (gramE σ J X)) ∧ (t ≠ 0 → ∀ (n : ℕ) (T : Matrix (Fin n) (Fin n) E) (Y : Fin (n + 1) → Fin (M + 1) → E), Y 0 = Fin.cons 1 (fun _ => 0) → gramE σ (blockOne (algebraMap F E t) J) Y = blockOne (algebraMap F E t) T → ∃ X, gramE σ J X = T ∧ Y = consTup X) := by
  first | exact @GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | exact GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg | (intros; apply GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.BlockOneScalarPreservesNondegenerate
section
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW GlobalTheory.CompanionTheory.SW.PiLocalization₂ NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

namespace GlobalTheory.CompanionTheory.SW.PiLocalization₂

theorem det_blockOne_eq_mul {K : Type} [CommRing K] {M : ℕ} (t : K) (A : Matrix (Fin M) (Fin M) K) :
    (blockOne t A).det = t * A.det := by
  rw [Matrix.det_succ_row_zero, Fin.sum_univ_succ]
  have hsub : (Matrix.of (Fin.cons (Fin.cons t fun _ ↦ 0) fun i ↦ Fin.cons 0 (A i)) :
      Matrix (Fin (M + 1)) (Fin (M + 1)) K).submatrix Fin.succ Fin.succ = A := by
    ext i j
    simp
  simp [blockOne, hsub]

theorem isHermND_blockOne_algebraMap : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ t : F, t ≠ 0 → IsHermND σ (blockOne (algebraMap F E t) J) := by
  intro F E _ _ _ _ _ σ M J hJ t ht
  refine ⟨fun i j => ?_, ?_⟩
  · refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j
    · simp [blockOne]
    · simp [blockOne]
    · simp [blockOne]
    · simpa [blockOne] using hJ.1 i j
  · rw [det_blockOne_eq_mul]
    exact mul_ne_zero ((map_ne_zero _).2 ht) hJ.2

end GlobalTheory.CompanionTheory.SW.PiLocalization₂
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DenominatorPowerSummableStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix Topology GlobalTheory.CompanionTheory.SW.Core
open scoped ENNReal NNReal MatrixGroups
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.denominator_power_summable : ∀ (F : Type) [Field F] [NumberField F], ∀ M : ℕ, 3 ≤ M → ∀ N : ℕ, 0 < N → (∀ (b : F) (r : 𝓞 F), den (b + (r : F)) = den b) ∧ (∀ b : F, 0 < den b) ∧ ∀ s : Set F, (∀ b ∈ s, ∀ b' ∈ s, (∃ r : 𝓞 F, b - b' = (N : F) * (r : F)) → b = b') → Summable fun b : s => ((den (b : F) : ℝ) ^ M)⁻¹ := by
  first | exact @GlobalTheory.CompanionTheory.SW.DenSum.summable_den | exact GlobalTheory.CompanionTheory.SW.DenSum.summable_den | (intros; apply GlobalTheory.CompanionTheory.SW.DenSum.summable_den <;> assumption)
end

-- bundled from CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.DisintegrationDensityFormulaStatement
section
open MeasureTheory Topology Matrix
open scoped ENNReal NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.exists_fibre_family_on_open_orbit : ∀ (V X Y : Type) [TopologicalSpace V] [LocallyCompactSpace V] [SecondCountableTopology V] [T2Space V] [MeasurableSpace V] [BorelSpace V] [TopologicalSpace X] [LocallyCompactSpace X] [SecondCountableTopology X] [T2Space X] [MeasurableSpace X] [BorelSpace X] (μ : Measure V) (ν : Measure X) [IsLocallyFiniteMeasure μ] [IsLocallyFiniteMeasure ν] [ν.IsOpenPosMeasure] (f : V → Y) (g : V → X) (ι : X → Y), Function.Injective ι → Continuous g → (∀ v, f v = ι (g v)) → ∀ (Q : Type) [Group Q] [TopologicalSpace Q] [IsTopologicalGroup Q] [LocallyCompactSpace Q] [SecondCountableTopology Q] [T2Space Q] [MulAction Q V] [ContinuousSMul Q V] [MulAction Q X] [ContinuousSMul Q X], (∀ (q : Q) (v : V), g (q • v) = q • g v) → ∀ (χ χ' : Q →* ℝ≥0), Continuous χ → Continuous χ' → (∀ q : Q, μ.map (fun v => q • v) = χ q • μ) → (∀ q : Q, ν.map (fun x => q • x) = χ' q • ν) → ∀ b₀ : X, IsOpenEmbedding (fun q : Q => q • b₀) → ∃ fib : X → Measure V, Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.IsFibreFamily μ f ι (g ⁻¹' (Set.range fun q : Q => q • b₀)) ν (Set.range fun q : Q => q • b₀) fib := by
  first | exact @GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit | exact GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit | (intros; apply GlobalTheory.CompanionTheory.SW.Slice.exists_isFibreFamily_openOrbit <;> assumption)
end

