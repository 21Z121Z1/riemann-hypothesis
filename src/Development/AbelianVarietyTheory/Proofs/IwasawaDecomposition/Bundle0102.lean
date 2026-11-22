import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0003
import Formalism.LocalRingCardinality.Bundle0007
import Formalism.LocalRingCardinality.Bundle0003
import Formalism.LocalRingCardinality.Lemmas
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.FiniteDimensionalWdSpace
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.QuotientMetricDivisors.Statement
import Formalism.HermitianLattices.StatementLat
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.MapSpanBaseChangeEquivSubmoduleOf
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.Bundle0003
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0073
import Formalism.LocalToGlobal.HilbertRowConditions.CenterIdempotentAction

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.InnerProductPositiveDefinite
section
open Formalism.BasicNotions NumberField IsDedekindDomain GlobalTheory.Mem

namespace GlobalTheory.Mem

theorem re_pos_of_majAt {K V ι M : Type} [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K]
    [AddCommGroup V] [Module K V] [Fintype ι] [DecidableEq ι] [AddCommGroup M] [Module ℂ M]
    (σ : K →+* ℂ) (b : Module.Basis ι K V) (X : InfinitePlace K → Matrix ι ι ℂ)
    (hX : IsUnit (X (InfinitePlace.mk σ)).det) (e : V →ₛₗ[σ] M) (Q : M →ₗ⋆[ℂ] M →ₗ[ℂ] ℂ)
    (h : ∀ x, (Formalism.HermitianLatticesTheory.majAt b X (InfinitePlace.mk σ) x x).re = (Q (e x) (e x)).re)
    (φ : M) (hφ : φ ∈ Submodule.span ℂ (Set.range fun a => e (b a))) (h0 : φ ≠ 0) :
    0 < (Q φ φ).re := by
  set v := InfinitePlace.mk σ with hv
  obtain ⟨ρ, hρc, hρρ, hρσ⟩ : ∃ ρ : ℂ →+* ℂ, Continuous ρ ∧ (∀ z, ρ (ρ z) = z) ∧
      ∀ x, ρ (v.embedding x) = σ x := by
    rcases InfinitePlace.embedding_mk_eq σ with h1 | h1
    · exact ⟨RingHom.id ℂ, continuous_id, fun _ => rfl, fun x => by rw [hv, h1]; rfl⟩
    · exact ⟨starRingEnd ℂ, Complex.continuous_conj, fun z => Complex.conj_conj z, fun x => by
        rw [hv, h1, ComplexEmbedding.conjugate_coe_eq, Complex.conj_conj]⟩
  have hd0 : DenseRange (Pi.map (fun _ : ι => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have key : ∀ w : ι → ℂ, (Q (∑ a, ρ (w a) • e (b a)) (∑ a, ρ (w a) • e (b a))).re =
      ∑ i, ‖((X v)⁻¹.mulVec w) i‖ ^ 2 := by
    intro w
    induction w using hd0.induction_on with
    | hp =>
      apply isClosed_eq
      · simp only [map_sum, LinearMap.map_smulₛₗ, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul,
          RingHom.id_apply]
        have := Complex.continuous_conj
        fun_prop
      · have : Continuous fun w : ι → ℂ => (X v)⁻¹.mulVec w :=
          Continuous.matrix_mulVec continuous_const continuous_id
        fun_prop
    | ih y =>
      have h1 := h (b.equivFun.symm y)
      have h2 : e (b.equivFun.symm y) =
          ∑ a, ρ (Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y a) • e (b a) := by
        rw [b.equivFun_symm_apply, map_sum]
        refine Finset.sum_congr rfl fun a _ => ?_
        rw [LinearMap.map_smulₛₗ, Pi.map_apply, hρσ]
      have h3 : Formalism.HermitianLatticesTheory.vecAt b v (b.equivFun.symm y) = Pi.map (fun _ : ι => (v.embedding : K → ℂ)) y := by
        funext a
        have : b.repr (b.equivFun.symm y) a = y a := by
          rw [← b.equivFun_apply, LinearEquiv.apply_symm_apply]
        simp only [Formalism.HermitianLatticesTheory.vecAt, this, Pi.map_apply]
      rw [← h2, ← h1, ← normAt_sq_eq_majAt, Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm,
        Real.sq_sqrt (Finset.sum_nonneg fun i _ => by positivity), Formalism.HermitianLatticesTheory.fcoord, h3]
  obtain ⟨z, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 hφ
  have hk := key fun a => ρ (z a)
  simp only [hρρ] at hk
  rw [hk]
  refine lt_of_le_of_ne (Finset.sum_nonneg fun i _ => by positivity) fun hs => h0 ?_
  have h4 : (X v)⁻¹.mulVec (fun a => ρ (z a)) = 0 := by
    funext i
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun i _ => by positivity)).1 hs.symm i (Finset.mem_univ i)
    simpa using this
  have h5 : (fun a => ρ (z a)) = 0 := by
    have := congrArg (X v).mulVec h4
    rwa [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv _ hX, Matrix.one_mulVec, Matrix.mulVec_zero] at this
  refine Finset.sum_eq_zero fun a _ => ?_
  have h6 : z a = 0 := by
    rw [← hρρ (z a), show ρ (z a) = 0 from congrFun h5 a, map_zero]
  rw [h6, zero_smul]

theorem ipC_zero_re_pos : ∀ (B : Base) (C : Cols B) (u : B.Word), (∀ φ ψ : (C.mem u).A.Mu0, (C.fm u).ipC 0 ψ φ = star ((C.fm u).ipC 0 φ ψ)) → ∀ φ : (C.mem u).A.Mu0, φ ≠ 0 → 0 < ((C.fm u).ipC 0 φ φ).re := by
  intro B C u _ φ hφ
  let Q : ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ⋆[ℂ] ((C.mem u).C.cls 0 → (C.mem u).C.Y 0 → ℂ) →ₗ[ℂ] ℂ :=
    LinearMap.mk₂'ₛₗ (starRingEnd ℂ) (RingHom.id ℂ) ((C.fm u).ipC 0)
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
      (fun x y z => by simp [MemberForms.ipC, mul_add, Finset.sum_add_distrib])
      (fun c x y => by simp [MemberForms.ipC, Finset.mul_sum, mul_left_comm])
  refine re_pos_of_majAt B.embLL ((C.fm u).lat 0).b ((C.fm u).lat 0).X (((C.fm u).lat_good 0).1 _)
    ((C.fm u).emb 0) Q ((C.fm u).emb_norm 0) φ ?_ (fun h => hφ (Subtype.ext h))
  rw [((C.fm u).emb_basis 0).2, (C.fm u).Fi_zero]
  exact φ.2

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsSstResToOfIsPst
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Polynomial TensorProduct Module GlobalTheory.Pst

namespace GlobalTheory.PstSst

variable {l : ℕ} [Fact l.Prime]

theorem apply_mem_kur (g : GQ l) (c : ↥(MaximalUnramifiedExtension l)) : g (c : Om l) ∈ MaximalUnramifiedExtension l := by
  have h : (MaximalUnramifiedExtension l).map (g : Om l →ₐ[ℚ_[l]] Om l) ≤ MaximalUnramifiedExtension l := by
    conv_lhs => rw [MaximalUnramifiedExtension, IntermediateField.adjoin_map]
    refine IntermediateField.adjoin.mono _ _ _ ?_
    rintro _ ⟨x, ⟨m, h0, hm, hx⟩, rfl⟩
    exact ⟨m, h0, hm, by rw [← map_pow, hx, map_one]⟩
  exact h ⟨c, c.2, rfl⟩

theorem mem_of_fixed (K : FinExt l) (x : Om l) (hx : ∀ g ∈ GK K, g x = x) : x ∈ K.1 := by
  have : IsGalois ℚ_[l] (Om l) := {}
  rw [← InfiniteGalois.fixedField_fixingSubgroup K.1, IntermediateField.mem_fixedField_iff]
  exact hx

def incl (K : FinExt l) : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) :=
  IntermediateField.inclusion (inf_le_right : K.1 ⊓ MaximalUnramifiedExtension l ≤ MaximalUnramifiedExtension l)

section

variable (P : LocPrime l) (LL : Type) [Field LL] [Algebra ℚ_[l] LL]
  (V : Type) [AddCommGroup V] [Module LL V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] LL V]

theorem mulV_smul (q : ℚ_[l]) (c : ↥(MaximalUnramifiedExtension l)) (x : V ⊗[ℚ_[l]] Bst P) :
    mulV P LL V (q • c) x = q • mulV P LL V c x := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul v b =>
    rw [mulV_tmul, mulV_tmul, ← tmul_smul, ← smul_mul_assoc]
    congr 2
    rw [Polynomial.algebraMap_apply, Polynomial.algebraMap_apply, smul_C]
    congr 1
    exact map_smul (IsScalarTower.toAlgHom ℚ_[l] ↥(MaximalUnramifiedExtension l) P.R.B) q c
  | add x y hx hy => rw [map_add, map_add, hx, hy, smul_add]

def comb (K' : FinExt l) {n : ℕ} (b : Fin n → V ⊗[ℚ_[l]] Bst P) :
    (Fin n → ↥(K0 K')) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P where
  toFun c := ∑ i, mulV P LL V (incl K' (c i)) (b i)
  map_add' c d := by simp [Finset.sum_add_distrib]
  map_smul' q c := by
    rw [RingHom.id_apply, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mulV_smul]
    exact congrArg (fun a => mulV P LL V a (b i)) (map_smul (incl K').toLinearMap q (c i))

variable {LL V} {K : FinExt l} (ρ : Representation LL ↥(GK K) V)

theorem coe_sum {n : ℕ} (b : Fin n → DpstUr P ρ) (c : Fin n → ↥(MaximalUnramifiedExtension l)) :
    (((toUr P ρ).symm (∑ i, c i • b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) =
      ∑ i, mulV P LL V (c i) (((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) : V ⊗[ℚ_[l]] Bst P) := by
  rw [map_sum, Submodule.coe_sum]
  rfl

theorem finrank_dst {n : ℕ} (b : Basis (Fin n) ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)) (K' : FinExt l) (h : K.1 ≤ K'.1)
    (hb : ∀ i (g : ↥(GK K)), (g : GQ l) ∈ GK K' →
      stRep P ρ g ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) = ((toUr P ρ).symm (b i) : ↥(Dpst P ρ))) :
    finrank ℚ_[l] ↥(Dst P (resTo ρ h)) = n * finrank ℚ_[l] ↥(K0 K') := by
  have := K'.2
  have hle : K0 K' ≤ K'.1 := inf_le_left
  have : FiniteDimensional ℚ_[l] ↥(K0 K') :=
    FiniteDimensional.of_injective (IntermediateField.inclusion hle).toLinearMap
      (IntermediateField.inclusion_injective hle)
  set β : Fin n → V ⊗[ℚ_[l]] Bst P := fun i => ((toUr P ρ).symm (b i) : ↥(Dpst P ρ)) with hβ
  have huniq : ∀ c d : Fin n → ↥(MaximalUnramifiedExtension l),
      ∑ i, mulV P LL V (c i) (β i) = ∑ i, mulV P LL V (d i) (β i) → c = d := by
    intro c d hcd
    rw [← coe_sum, ← coe_sum] at hcd
    have h1 := (toUr P ρ).symm.injective (Subtype.ext hcd)
    rw [← b.equivFun_symm_apply, ← b.equivFun_symm_apply] at h1
    exact b.equivFun.symm.injective h1
  have hact : ∀ (g : ↥(GK K)), (g : GQ l) ∈ GK K' → ∀ c : Fin n → ↥(MaximalUnramifiedExtension l),
      stRep P ρ g (∑ i, mulV P LL V (c i) (β i)) =
        ∑ i, mulV P LL V ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ (β i) := by
    intro g hg c
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← End.mul_apply, stRep_mulV P ρ g (c i) ⟨_, apply_mem_kur (g : GQ l) (c i)⟩ rfl, End.mul_apply,
      hb i g hg]
  have hinj : Function.Injective (comb P LL V K' β) := fun c d hcd =>
    funext fun i => (incl K').injective (congrFun (huniq _ _ hcd) i)
  have hrange : LinearMap.range (comb P LL V K' β) = (Dst P (resTo ρ h)).restrictScalars ℚ_[l] := by
    ext x
    rw [Submodule.restrictScalars_mem]
    constructor
    · rintro ⟨c, rfl⟩
      refine (mem_Dst_resTo P ρ h).mpr fun g hg => ?_
      refine (hact g hg fun i => incl K' (c i)).trans (Finset.sum_congr rfl fun i _ => ?_)
      congr 2
      exact Subtype.ext (mem_GK.mp hg _ (c i).2.1)
    · intro hx
      let c : Fin n → ↥(MaximalUnramifiedExtension l) := b.repr (toUr P ρ ⟨x, Dst_resTo_le P ρ h hx⟩)
      have hc : ∑ i, mulV P LL V (c i) (β i) = x := by
        rw [← coe_sum, b.sum_repr, AddEquiv.symm_apply_apply]
      have hK : ∀ i, (c i : Om l) ∈ K'.1 := fun i => mem_of_fixed K' _ fun g hg => by
        have h1 := hact ⟨g, GK_le h hg⟩ hg c
        rw [hc, (mem_Dst_resTo P ρ h).mp hx ⟨g, GK_le h hg⟩ hg, ← hc] at h1
        exact (congrArg Subtype.val (congrFun (huniq _ _ h1) i)).symm
      exact ⟨fun i => ⟨c i, hK i, (c i).2⟩, hc⟩
  have h1 := LinearMap.finrank_range_of_inj hinj
  rw [hrange, finrank_pi_fintype] at h1
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul] at h1
  exact h1

end

theorem isSst_resTo_of_isPst (l : ℕ) [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l) (V : Type)
    [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V]
    [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V) (hV : IsPst P ρ) :
    ∃ (K₁ : FinExt l), K.1 ≤ K₁.1 ∧
      ∀ (K' : FinExt l) (h : K.1 ≤ K'.1), K₁.1 ≤ K'.1 → IsSst P (resTo ρ h) := by
  have := LL.2
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  obtain ⟨_, hdim⟩ := (isPst_iff P ρ).mp hV
  let b := finBasis ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)
  choose F hF using fun i => (mem_Dpst P ρ).mp ((toUr P ρ).symm (b i)).2
  have := fun i => (F i).2
  refine ⟨supExt K ⟨⨆ i, (F i).1, inferInstance⟩, le_sup_left, fun K' h h₁ => ?_⟩
  have h1 := finrank_dst P ρ b K' h fun i g hg =>
    hF i g (GK_le (K := F i) (((le_iSup (fun i => (F i).1) i).trans le_sup_right).trans h₁) hg)
  rw [hdim, ← finrank_mul_finrank ℚ_[l] ↥LL.1 V, ← finrank_mul_finrank ℚ_[l] ↥LL.1, mul_assoc] at h1
  rw [IsSst, mul_comm]
  exact Nat.eq_of_mul_eq_mul_left finrank_pos h1

end GlobalTheory.PstSst
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LatticeIndexNonzeroIffUnderFieldMap
section
open NumberField IsDedekindDomain IsLocalRing TensorProduct

namespace GlobalTheory.LidxBaseChange

theorem length_eq_of_residue (R O M : Type*) [CommRing R] [CommRing O] [IsLocalRing O] [Algebra R O]
    [AddCommGroup M] [Module R M] [Module O M] [IsScalarTower R O M]
    (h1 : Module.length R (ResidueField O) = 1) : Module.length R M = Module.length O M := by
  have step : ∀ {p q : Submodule O M}, p ⋖ q → Module.length R q = Module.length R p + 1 := by
    intro p q h
    let f : p →ₗ[O] q := Submodule.inclusion h.le
    have key : IsSimpleModule O (q ⧸ f.range) := by
      rwa [Submodule.range_inclusion, ← covBy_iff_quot_is_simple h.le]
    obtain ⟨m, hm, ⟨e⟩⟩ := isSimpleModule_iff_quot_maximal.mp key
    rw [eq_maximalIdeal hm] at e
    let g : q →ₗ[O] ResidueField O := e.comp f.range.mkQ
    have : Function.Injective f := Submodule.inclusion_injective _
    have : Function.Surjective g := e.surjective.comp f.range.mkQ_surjective
    have : Function.Exact f g := LinearMap.exact_iff.mpr ((e.ker_comp f.range.mkQ).trans f.range.ker_mkQ)
    rw [Module.length_eq_add_of_exact (f.restrictScalars R) (g.restrictScalars R)
      (by simpa) (by simpa) (by simpa), h1]
  by_cases h : IsFiniteLength O M
  · obtain ⟨s, hs_bot, hs_top⟩ := isFiniteLength_iff_exists_compositionSeries.mp h
    rw [← Module.length_compositionSeries s hs_bot hs_top]
    suffices ∀ k, Module.length R (s k) = k by
      rw [← Fin.val_last s.length, ← this, ← RelSeries.last, hs_top]
      exact Module.length_top.symm
    intro k
    induction k using Fin.induction with
    | zero => rw [← RelSeries.head, hs_bot]; simp
    | succ i hi => simpa [hi] using step (s.step i)
  · have : ¬ IsFiniteLength R M := by
      contrapose! h
      rw [isFiniteLength_iff_isNoetherian_isArtinian] at h ⊢
      exact h.imp (isNoetherian_of_tower R) (isArtinian_of_tower R)
    rw [← Module.length_ne_top_iff, not_ne_iff] at h this
    rw [h, this]

theorem length_residue_atPrime {R : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] :
    Module.length R (ResidueField (Localization.AtPrime P)) = 1 := by
  rw [Module.length_eq_of_surjective (S := R) (R := ResidueField (Localization.AtPrime P))
    (Ideal.algebraMap_residueField_surjective P)]
  simp

theorem mem_localization_iff {R W : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X : Submodule R W) (x : W) :
    x ∈ Formalism.HermitianLatticesTheory.localization₂ P X ↔ x ∈ Submodule.span (Localization.AtPrime P) (X : Set W) := by
  constructor
  · rintro ⟨s, hs, hx⟩
    obtain ⟨u, hu⟩ := IsLocalization.map_units (Localization.AtPrime P) (⟨s, hs⟩ : P.primeCompl)
    have : x = (↑u⁻¹ : Localization.AtPrime P) • (s • x) := by
      rw [← algebraMap_smul (Localization.AtPrime P) s x]
      change x = _ • (algebraMap R (Localization.AtPrime P) ((⟨s, hs⟩ : P.primeCompl) : R)) • x
      rw [← hu, smul_smul, Units.inv_mul, one_smul]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hx)
  · intro hx
    induction hx using Submodule.span_induction with
    | mem y hy => exact ⟨1, P.primeCompl.one_mem, by simpa using hy⟩
    | zero => exact Submodule.zero_mem _
    | add y z _ _ hy hz => exact Submodule.add_mem _ hy hz
    | smul c y _ hy =>
      obtain ⟨s, hs, hy⟩ := hy
      obtain ⟨⟨a, t⟩, h⟩ := IsLocalization.surj P.primeCompl c
      refine ⟨s * t, P.primeCompl.mul_mem hs t.2, ?_⟩
      have : (s * (t : R)) • c • y = a • s • y := by
        rw [mul_smul, ← algebraMap_smul (Localization.AtPrime P) (t : R), smul_smul _ c, mul_comm _ c]
        dsimp only at h
        rw [h, algebraMap_smul, smul_comm]
      rw [this]
      exact X.smul_mem a hy

theorem length_localized_eq₂ {R W : Type*} [CommRing R] (P : Ideal R) [P.IsMaximal] [AddCommGroup W] [Module R W]
    [Module (Localization.AtPrime P) W] [IsScalarTower R (Localization.AtPrime P) W] (X Y : Submodule R W) :
    Module.length R (↥(Formalism.HermitianLatticesTheory.localization₂ P X) ⧸ (Formalism.HermitianLatticesTheory.localization₂ P Y).comap (Formalism.HermitianLatticesTheory.localization₂ P X).subtype) =
      Module.length (Localization.AtPrime P) (↥(Submodule.span (Localization.AtPrime P) (X : Set W)) ⧸
        (Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype) := by
  rw [← length_eq_of_residue R _ _ (length_residue_atPrime P)]
  have hX : Formalism.HermitianLatticesTheory.localization₂ P X = (Submodule.span (Localization.AtPrime P) (X : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P X x
  have hY : Formalism.HermitianLatticesTheory.localization₂ P Y = (Submodule.span (Localization.AtPrime P) (Y : Set W)).restrictScalars R :=
    Submodule.ext fun x => mem_localization_iff P Y x
  rw [hX, hY]
  exact (Submodule.Quotient.restrictScalarsEquiv R ((Submodule.span (Localization.AtPrime P) (Y : Set W)).comap
          (Submodule.span (Localization.AtPrime P) (X : Set W)).subtype)).length_eq

theorem span_image_inf {A O V W : Type*} [CommRing A] [CommRing O] [Algebra A O] [Module.Flat A O]
    [AddCommGroup V] [Module A V] [AddCommGroup W] [Module A W] [Module O W] [IsScalarTower A O W]
    (φ : V →ₗ[A] W) (h : Function.Injective (φ.liftBaseChange O)) (M N : Submodule A V) :
    Submodule.span O (φ '' (M : Set V)) ⊓ Submodule.span O (φ '' (N : Set V)) =
      Submodule.span O (φ '' ((M ⊓ N : Submodule A V) : Set V)) := by
  have key : ∀ X : Submodule A V,
      Submodule.span O (φ '' (X : Set V)) = (X.baseChange O).map (φ.liftBaseChange O) := fun X => by
    rw [Submodule.baseChange_eq_span, Submodule.map_span, Submodule.map_coe, Set.image_image]
    congr 1
    exact Set.image_congr fun v _ => by simp
  rw [key, key, key, baseChange_inf, Submodule.map_inf _ h]

theorem exists_lidx_eq_mul (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] [Algebra K K']
    {d d' : ℕ} (ψ : (Fin d → K) →ₗ[K] (Fin d' → K')) (hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)))
    (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')) [P'.asIdeal.LiesOver P.asIdeal] :
    ∃ e : ℕ, 0 < e ∧ ∀ A B : Submodule (𝓞 K) (Fin d → K),
      Formalism.HermitianLatticesTheory.lidx P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (A : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (B : Set (Fin d → K)))) = Formalism.HermitianLatticesTheory.lidx P.asIdeal A B * e := by
  have hPm := P.isMaximal
  have hPm' := P'.isMaximal
  let O := Localization.AtPrime P.asIdeal
  let O' := Localization.AtPrime P'.asIdeal
  letI : Algebra O K := IsLocalization.localizationAlgebraOfSubmonoidLe O K P.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K)) P.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K) O K := IsLocalization.localization_isScalarTower_of_submonoid_le O K _ _ _
  letI : Algebra O' K' := IsLocalization.localizationAlgebraOfSubmonoidLe O' K' P'.asIdeal.primeCompl
    (nonZeroDivisors (𝓞 K')) P'.asIdeal.primeCompl_le_nonZeroDivisors
  have : IsScalarTower (𝓞 K') O' K' := IsLocalization.localization_isScalarTower_of_submonoid_le O' K' _ _ _
  have : IsFractionRing O K := IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P.asIdeal.primeCompl O K
  have : IsFractionRing O' K' :=
    IsFractionRing.isFractionRing_of_isDomain_of_isLocalization P'.asIdeal.primeCompl O' K'
  have : IsScalarTower (𝓞 K) O' K' := IsScalarTower.of_algebraMap_eq fun x => by
    rw [IsScalarTower.algebraMap_apply (𝓞 K) (𝓞 K') O', ← IsScalarTower.algebraMap_apply (𝓞 K') O' K',
      ← IsScalarTower.algebraMap_apply]
  letI : Algebra O O' := Localization.AtPrime.algebraOfLiesOver P.asIdeal P'.asIdeal
  have : Localization.AtPrime.IsLiesOverAlgebra P.asIdeal P'.asIdeal := ⟨rfl⟩
  have : IsScalarTower (𝓞 K) O O' := inferInstance
  have : IsLocalHom (algebraMap O O') := inferInstance
  have : IsDiscreteValuationRing O :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K) P.ne_bot _
  have : IsDiscreteValuationRing O' :=
    IsLocalization.AtPrime.isDiscreteValuationRing_of_dedekind_domain (𝓞 K') P'.ne_bot _
  have : FaithfulSMul O O' := inferInstance
  have : Module.Flat O O' := inferInstance
  have : IsLocalHom (algebraMap O O) := inferInstance
  refine ⟨(maximalIdeal O').ramificationIdx O, ramificationIdx_maximalIdeal_pos O O', ?_⟩
  have hlen : ∀ M N : Submodule (𝓞 K) (Fin d → K), N ≤ M →
      Formalism.HermitianLatticesTheory.locLen P'.asIdeal (Submodule.span (𝓞 K') (ψ '' (M : Set (Fin d → K))))
        (Submodule.span (𝓞 K') (ψ '' (N : Set (Fin d → K)))) =
        Formalism.HermitianLatticesTheory.locLen P.asIdeal M N * (maximalIdeal O').ramificationIdx O := by
    intro M N hNM
    unfold Formalism.HermitianLatticesTheory.locLen
    rw [length_localized_eq₂, length_localized_eq₂, Submodule.span_span_of_tower, Submodule.span_span_of_tower]
    have h1 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O' K') ψ _ hψ N M hNM
    have h2 := Formalism.BasicNotions.FBC.length_flat_tower P.asIdeal (IsFractionRing.injective O K)
      (LinearMap.id : (Fin d → K) →ₗ[K] (Fin d → K)) (Pi.basisFun K (Fin d))
      (Pi.basisFun K (Fin d)).linearIndependent N M hNM
    rw [length_fibre_eq_ramificationIdx O O'] at h1
    have h3 : Module.length O (O ⧸ (maximalIdeal O).map (algebraMap O O)) = 1 := by
      rw [Algebra.algebraMap_self, Ideal.map_id]
      have h4 := IsDiscreteValuationRing.length_quotient_pow_maximalIdeal O 1
      rw [pow_one] at h4
      exact_mod_cast h4
    rw [h3, mul_one, LinearMap.id_coe, Set.image_id, Set.image_id] at h2
    rw [h1, h2, ENat.toNat_mul, ENat.toNat_coe]
  intro A B
  have hinj := Formalism.BasicNotions.FBC.liftBaseChange_injective_top (A := 𝓞 K) (IsFractionRing.injective (𝓞 K') K') ψ _ hψ
  have hinf := span_image_inf _ hinj A B
  unfold Formalism.HermitianLatticesTheory.lidx
  erw [hinf]
  erw [hlen A _ inf_le_left, hlen B _ inf_le_right]
  push_cast
  ring

theorem lidx_ne_zero_iff : ∀ (K K' : Type) [Field K] [NumberField K] [Field K'] [NumberField K'] (φ : K →+* K') (d d' : ℕ) (G : Matrix (Fin d') (Fin d) K'),
  Function.Bijective G.mulVec → ∀ (P : HeightOneSpectrum (𝓞 K)) (P' : HeightOneSpectrum (𝓞 K')),
  (∀ (x : 𝓞 K) (x' : 𝓞 K'), φ (x : K) = (x' : K') → (x ∈ P.asIdeal ↔ x' ∈ P'.asIdeal)) →
  ∀ A B : Submodule (𝓞 K) (Fin d → K), A.FG → B.FG →
    (Formalism.HermitianLatticesTheory.lidx P.asIdeal A B ≠ 0 ↔ Formalism.HermitianLatticesTheory.lidx P'.asIdeal
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (A : Set (Fin d → K))))
      (Submodule.span (𝓞 K') ((fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) '' (B : Set (Fin d → K)))) ≠ 0) := by
  intro K K' _ _ _ _ φ d d' G hG P P' hP A B _ _
  letI : Algebra K K' := φ.toAlgebra
  have : P'.asIdeal.LiesOver P.asIdeal := ⟨Ideal.ext fun x => hP x (algebraMap (𝓞 K) (𝓞 K') x) rfl⟩
  let ψ : (Fin d → K) →ₗ[K] (Fin d' → K') :=
    (G.mulVecLin.restrictScalars K) ∘ₗ (Algebra.linearMap K K').compLeft (Fin d)
  have hψ : LinearIndependent K' (ψ ∘ Pi.basisFun K (Fin d)) := by
    have h := (Pi.basisFun K' (Fin d)).linearIndependent.map' G.mulVecLin (LinearMap.ker_eq_bot.2 hG.1)
    have e : ψ ∘ Pi.basisFun K (Fin d) = G.mulVecLin ∘ Pi.basisFun K' (Fin d) := by
      funext i
      simp only [ψ, Function.comp_apply, LinearMap.comp_apply, LinearMap.restrictScalars_apply]
      congr 1
      funext k
      by_cases hk : k = i <;> simp [hk, Pi.single_apply]
    rw [e]
    exact h
  obtain ⟨e, he, h⟩ := exists_lidx_eq_mul K K' ψ hψ P P'
  have h' := h A B
  have hf : (fun x : Fin d → K => Matrix.mulVec G fun k => φ (x k)) = ψ := rfl
  rw [hf, h']
  simp [he.ne']

end GlobalTheory.LidxBaseChange
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.PosDefMapEmbeddingOfPositiveAtPlace
section
open NumberField Formalism.L2.DIV Formalism.L2.Rows GlobalTheory.AmbCrd
open scoped Matrix ComplexOrder

namespace GlobalTheory.AmbTiePosDef

variable {K : Type} [Field K] [NumberField K] [StarRing K]

theorem hAt_eq_dotProduct {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (x y : Fin n → K) :
    hAt H v x y = star (fun i => v.embedding (x i)) ⬝ᵥ (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) := by
  simp only [hAt, dotProduct, Matrix.mulVec, Matrix.map_apply, Finset.mul_sum, Pi.star_apply, mul_assoc]

theorem hAt_single_single {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K) (i j : Fin n) :
    hAt H v (Pi.single i 1) (Pi.single j 1) = v.embedding (H i j) := by
  simp [hAt, Pi.single_apply]

theorem posDef_map_of_posAt [IsTotallyComplex K] {n : ℕ} (H : Matrix (Fin n) (Fin n) K) (v : InfinitePlace K)
    (h : PosAt H v) : (H.map v.embedding).PosDef := by
  have herm : (H.map v.embedding).IsHermitian := by
    ext i j
    have := h.1 (Pi.single j 1) (Pi.single i 1)
    rw [hAt_single_single, hAt_single_single] at this
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply]
    rw [this]
  have hd : DenseRange (Pi.map (fun _ : Fin n => (v.embedding : K → ℂ))) :=
    DenseRange.piMap (fun _ => Formalism.BasicNotions.denseRange_embedding_of_isComplex v (IsTotallyComplex.isComplex v))
  have psd : (H.map v.embedding).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg herm fun z => ?_
    induction z using hd.induction_on with
    | hp =>
      refine isClosed_le continuous_const ?_
      exact Continuous.dotProduct (continuous_star) (Continuous.matrix_mulVec continuous_const continuous_id)
    | ih y =>
      have hy : Pi.map (fun _ : Fin n => (v.embedding : K → ℂ)) y = fun i => v.embedding (y i) := rfl
      rw [hy, ← hAt_eq_dotProduct]
      have hs := h.1 y y
      have him : (hAt H v y y).im = 0 := by
        have := congrArg Complex.im hs
        simp at this
        linarith
      rw [Complex.nonneg_iff]
      refine ⟨?_, him.symm⟩
      by_cases hy0 : y = 0
      · subst hy0
        simp [hAt]
      · exact (h.2 y hy0).le
  rw [psd.posDef_iff_det_ne_zero]
  show (v.embedding.mapMatrix H).det ≠ 0
  rw [← RingHom.map_det]
  intro h0
  rw [map_eq_zero] at h0
  obtain ⟨y, hy0, hHy⟩ := Matrix.exists_mulVec_eq_zero_iff.2 h0
  have hz : hAt H v y y = 0 := by
    rw [hAt_eq_dotProduct]
    have : (H.map v.embedding) *ᵥ (fun i => v.embedding (y i)) = 0 := by
      funext i
      have := RingHom.map_mulVec v.embedding H y i
      rw [hHy] at this
      simpa [Function.comp_def] using this.symm
    rw [this, dotProduct_zero]
  have := h.2 y hy0
  rw [hz] at this
  simp at this

end GlobalTheory.AmbTiePosDef
end

