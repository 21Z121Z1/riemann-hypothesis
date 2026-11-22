import Development.AbelianVarietyTheory.Proofs.DivisorProofs.T2SpaceFiniteAdeleRing
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1284
import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0049
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1236
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0024
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0104
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1254
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0831
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1276
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1217
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1286
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1252
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.IsSubquotientDetRepParInd

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemCompactPartRestrictedProductIffForall
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.CptPartRestr

open Set
open scoped Pointwise

variable {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [T2Space G]

def cptSub (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) : Subgroup G where
  carrier := {t | t ∈ T ∧ IsCompact (closure (Subgroup.zpowers t : Set G))}
  one_mem' := by
    refine ⟨T.one_mem, ?_⟩
    rw [Subgroup.zpowers_one_eq_bot, Subgroup.coe_bot, closure_singleton]
    exact isCompact_singleton
  mul_mem' := by
    rintro a b ⟨haT, ha⟩ ⟨hbT, hb⟩
    refine ⟨T.mul_mem haT hbT, ?_⟩
    have hc : Commute a b := hT a haT b hbT
    have hsub : closure (Subgroup.zpowers (a * b) : Set G) ⊆
        closure (Subgroup.zpowers a : Set G) * closure (Subgroup.zpowers b : Set G) := by
      refine closure_minimal ?_ (ha.mul hb).isClosed
      rintro _ ⟨n, rfl⟩
      simp only [hc.mul_zpow]
      exact Set.mul_mem_mul (subset_closure (Subgroup.zpow_mem_zpowers a n))
        (subset_closure (Subgroup.zpow_mem_zpowers b n))
    exact (ha.mul hb).of_isClosed_subset isClosed_closure hsub
  inv_mem' := by
    rintro a ⟨haT, ha⟩
    refine ⟨T.inv_mem haT, ?_⟩
    rw [Subgroup.zpowers_inv]
    exact ha

theorem mem_cptPart_iff (T : Subgroup G) (hT : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a) (x : G) :
    x ∈ cptPart T ↔ x ∈ T ∧ IsCompact (closure (Subgroup.zpowers x : Set G)) := by
  have : cptPart T = cptSub T hT := Subgroup.closure_eq (cptSub T hT)
  rw [this]
  rfl

section Restr

variable {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X]
  [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)]
  {pf : ∀ v, X →* Y v} {K : ∀ v, Subgroup (Y v)}

theorem isClosed_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (C : ∀ v, Set (Y v)) (hC : ∀ v, IsCompact (C v)) : IsClosed {z : X | ∀ v, pf v z ∈ C v} := by
  simp only [Set.setOf_forall]
  exact isClosed_iInter fun v => (hC v).isClosed.preimage (hX.continuous_pf v)

theorem isCompact_setOf_forall_mem (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K)
    (S : Finset V) : ∀ C : ∀ v, Set (Y v), (∀ v, IsCompact (C v)) → (∀ v ∉ S, C v ⊆ K v) →
      IsCompact {z : X | ∀ v, pf v z ∈ C v} := by
  induction S using Finset.induction_on with
  | empty =>
    intro C hC hCK
    have hKg := hX.isCompact_level (fun e => e.elim) (fun e => e.elim)
    exact hKg.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC)
      fun z hz => ⟨fun e => e.elim, fun v => hCK v (Finset.notMem_empty v) (hz v)⟩
  | @insert v₀ S hv₀ ih =>
    intro C hC hCK
    obtain ⟨t, hcov⟩ := (hC v₀).elim_finite_subcover (fun c : C v₀ => (c : Y v₀) • (K v₀ : Set (Y v₀)))
      (fun c => (hX.isOpen_K v₀).smul _)
      (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, ⟨1, (K v₀).one_mem, by simp⟩⟩)
    set C' : ∀ v, Set (Y v) := Function.update C v₀ (K v₀ : Set (Y v₀)) with hC'def
    have hC' : ∀ v, IsCompact (C' v) := by
      intro v
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact hX.isCompact_K v
      · simp only [hC'def, Function.update_of_ne h]; exact hC v
    have hC'K : ∀ v ∉ S, C' v ⊆ K v := by
      intro v hv
      by_cases h : v = v₀
      · subst h; simp only [hC'def, Function.update_self]; exact subset_rfl
      · simp only [hC'def, Function.update_of_ne h]
        exact hCK v (by simp [h, hv])
    have hM' := ih C' hC' hC'K
    have hl : ∀ c : Y v₀, ∃ x : X, ∀ v, pf v x = Pi.mulSingle v₀ c v := by
      intro c
      have hev : ∀ᶠ v in cofinite, (Pi.mulSingle v₀ c : ∀ v, Y v) v ∈ K v := by
        rw [Filter.eventually_cofinite]
        refine (Set.finite_singleton v₀).subset fun v hv => ?_
        by_contra h
        exact hv (by rw [Pi.mulSingle_eq_of_ne h]; exact (K v).one_mem)
      obtain ⟨x, -, hx⟩ := hX.exists_eq (fun e => e.elim) _ hev
      exact ⟨x, hx⟩
    choose xc hxc using hl
    have hU : IsCompact (⋃ i ∈ t, xc (i : Y v₀) • {z : X | ∀ v, pf v z ∈ C' v}) :=
      t.isCompact_biUnion fun i _ => hM'.smul _
    refine hU.of_isClosed_subset (isClosed_setOf_forall_mem hX C hC) fun z hz => ?_
    obtain ⟨i, hi, hzi⟩ := Set.mem_iUnion₂.1 (hcov (hz v₀))
    obtain ⟨k, hk, hik⟩ := Set.mem_smul_set.1 hzi
    refine Set.mem_iUnion₂.2 ⟨i, hi, Set.mem_smul_set_iff_inv_smul_mem.2 fun v => ?_⟩
    rw [smul_eq_mul, map_mul, map_inv, hxc]
    by_cases h : v = v₀
    · subst h
      simp only [Pi.mulSingle_eq_same, hC'def, Function.update_self]
      rw [← hik, smul_eq_mul, inv_mul_cancel_left]
      exact hk
    · simp only [Pi.mulSingle_eq_of_ne h, inv_one, one_mul, hC'def, Function.update_of_ne h]
      exact hz v

theorem isCompact_closure_zpowers_iff (hX : GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K) (x : X) :
    IsCompact (closure (Subgroup.zpowers x : Set X)) ↔
      ∀ v, IsCompact (closure (Subgroup.zpowers (pf v x) : Set (Y v))) := by
  constructor
  · intro h v
    have hi := h.image (hX.continuous_pf v)
    refine hi.of_isClosed_subset isClosed_closure (closure_minimal ?_ hi.isClosed)
    rintro _ ⟨n, rfl⟩
    exact ⟨x ^ n, subset_closure (Subgroup.zpow_mem_zpowers x n), map_zpow _ _ _⟩
  · intro h
    have hfin := Filter.eventually_cofinite.1 (hX.eventually_mem x)
    have hCK : ∀ v ∉ hfin.toFinset, closure (Subgroup.zpowers (pf v x) : Set (Y v)) ⊆ K v := by
      intro v hv
      rw [Set.Finite.mem_toFinset, Set.mem_setOf_eq, not_not] at hv
      exact closure_minimal (fun y hy => Subgroup.zpowers_le.2 hv hy) (hX.isCompact_K v).isClosed
    have hM := isCompact_setOf_forall_mem hX hfin.toFinset _ h hCK
    refine hM.of_isClosed_subset isClosed_closure
      (closure_minimal ?_ (isClosed_setOf_forall_mem hX _ h))
    rintro _ ⟨n, rfl⟩ v
    rw [map_zpow]
    exact subset_closure (Subgroup.zpow_mem_zpowers _ n)

end Restr

theorem mem_cptPart_iff_forall : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [IsTopologicalGroup X] [T2Space X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] [∀ v, IsTopologicalGroup (Y v)] [∀ v, T2Space (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (T : Subgroup X) (Tv : ∀ v, Subgroup (Y v)), (∀ x, x ∈ T ↔ ∀ v, pf v x ∈ Tv v) → (∀ v, ∀ a ∈ Tv v, ∀ b ∈ Tv v, a * b = b * a) → ∀ x, x ∈ cptPart T ↔ ∀ v, pf v x ∈ cptPart (Tv v) := by
  intro X V Y _ _ _ _ _ _ _ _ pf K hX T Tv hT hTv x
  have hTc : ∀ a ∈ T, ∀ b ∈ T, a * b = b * a := fun a ha b hb =>
    hX.ext _ _ (fun e => e.elim) fun v => by
      rw [map_mul, map_mul]; exact hTv v _ ((hT a).1 ha v) _ ((hT b).1 hb v)
  rw [mem_cptPart_iff T hTc, hT, isCompact_closure_zpowers_iff hX]
  simp only [mem_cptPart_iff _ (hTv _)]
  exact ⟨fun h v => ⟨h.1 v, h.2 v⟩, fun h => ⟨fun v => (h v).1, fun v => (h v).2⟩⟩

end GlobalTheory.CptPartRestr
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemFiniteUnitIdelesOfMapMaxRealSubfield
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.UnitDown

theorem exists_above {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (v : HeightOneSpectrum (𝓞 F)) : ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 F) = v := by
  haveI := v.isMaximal
  obtain ⟨P, hPm, hP⟩ := Ideal.exists_maximal_ideal_liesOver_of_isIntegral (S := 𝓞 E) v.asIdeal
  have hne : P ≠ ⊥ := by
    intro h
    apply v.ne_bot
    rw [hP.over, h]
    exact Ideal.comap_bot_of_injective _ (FaithfulSMul.algebraMap_injective (𝓞 F) (𝓞 E))
  refine ⟨⟨P, hPm.isPrime, hne⟩, ?_⟩
  ext1
  rw [HeightOneSpectrum.under_asIdeal]
  exact hP.over.symm

theorem unit_down : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (b : Neutral.B1.Ideles (maximalRealSubfield E)),
    GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b ∈ GlobalTheory.Mem.Chr.unitIdl E → b ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) := by
  intro E _ _ _ b hb v
  obtain ⟨w, rfl⟩ := exists_above (E := E) v
  have h := hb w
  have e : ((GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.ideleMap (maximalRealSubfield E) E b : AdeleRing (𝓞 E) E).2 w) =
      GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap (maximalRealSubfield E) E w
        ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _)) := rfl
  rw [e, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap] at h
  have he : (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 :=
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under _).ne_bot
  set x := Valued.v ((b : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 (w.under _))
  set n := (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal
  have h' : x ^ n = 1 := h
  rcases lt_trichotomy x 1 with hx | hx | hx
  · exact absurd h' (pow_lt_one₀ zero_le' hx he).ne
  · exact hx
  · exact absurd h' (one_lt_pow₀ hx he).ne'

end GlobalTheory.UnitDown
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemIsotropicFlagLeviOfKeepsWeights
section
open NumberField MeasureTheory Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut
open scoped TensorProduct
open GlobalTheory.Mem.UnipCocompact

namespace GlobalTheory.UAut

theorem exists_blockTriangular_of_keeps_weights {A ι : Type} [CommRing A] [Fintype ι] {n r : ℕ}
    {ε : ι → Matrix (Fin n) (Fin n) A} {w : ι → ℤ} (h1 : ∑ a, ε a = 1) {C : Matrix (Fin n) (Fin r) A}
    {L : Matrix (Fin r) (Fin n) A} (hL : L * C = 1) (e : Fin r → ι) (he : ∀ j, ε (e j) = C * single j j (1 : A) * L)
    {d : Fin r → ℕ} (hw : ∀ a j, w a = w (e j) → ∃ i, a = e i) (hd : ∀ i j, d j < d i → w (e i) ≠ w (e j))
    {z : Matrix (Fin n) (Fin n) A} (hz : ∀ a b, w a ≠ w b → ε a * z * ε b = 0) :
    ∃ B : Matrix (Fin r) (Fin r) A, B.BlockTriangular d ∧ z * C = C * B := by
  refine ⟨L * z * C, fun i j hij => ?_, ?_⟩
  · have := hz _ _ (hd i j hij)
    rw [he, he] at this
    exact (sandwich_eq_zero hL z j i).1 this
  · have h2 : (1 - C * L) * C = 0 := by
      rw [Matrix.sub_mul, Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.one_mul, sub_self]
    have h3 : ∀ j, (1 - C * L) * (z * ε (e j)) = 0 := fun j => by
      rw [← Matrix.one_mul (z * ε (e j)), ← h1, Finset.sum_mul, h1, Finset.mul_sum]
      refine Finset.sum_eq_zero fun a _ => ?_
      by_cases h : w a = w (e j)
      · obtain ⟨i, rfl⟩ := hw a j h
        rw [← Matrix.mul_assoc, he i, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← Matrix.mul_assoc, h2]
        simp
      · rw [← Matrix.mul_assoc (ε a), hz _ _ h, Matrix.mul_zero]
    have h4 : ∑ j, ε (e j) = C * L := by
      simp only [he]
      rw [← Matrix.sum_mul, ← Matrix.mul_sum, Matrix.sum_single_one, Matrix.mul_one]
    have h5 : (1 - C * L) * (z * (C * L)) = 0 := by
      conv_lhs => rw [← h4, Finset.mul_sum, Finset.mul_sum, h4]
      exact Finset.sum_eq_zero fun j _ => h3 j
    have h6 := congrArg (· * C) h5
    simp only [Matrix.mul_assoc, hL, Matrix.mul_one, Matrix.zero_mul] at h6
    rw [Matrix.sub_mul, Matrix.one_mul, sub_eq_zero] at h6
    rw [h6]
    simp only [Matrix.mul_assoc]

theorem mem_leviFlag_of_keeps_weights : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E) (d : Fin r → ℕ) (M : ℕ), (∀ j, d j < M) → Formalism.UG.cT (σ : E →+* E) X * J * X = 0 → Formalism.UG.cT (σ : E →+* E) Y * J * Y = 0 → Formalism.UG.cT (σ : E →+* E) X * J * Y = 1 → ∀ g : GAd σ J, (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → (∀ a b, wt d M a ≠ wt d M b → fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) a * (matHom (AF F) σ J g⁻¹).1 * fam (adjA σ J) (idemA X (Formalism.UG.cT (σ : E →+* E) Y * J)) b = 0) → g ∈ leviFlag σ J X Y d := by
  intro F E _ _ _ _ _ σ hCM n J hJ r X Y d M hd _ _ xy g hg hg'
  have hσ : ∀ x, σ (σ x) = x := sigma_sigma hCM
  have cc : ∀ {m p : Type} (A : Matrix m p E), Formalism.UG.cT (σ : E →+* E) (Formalism.UG.cT (σ : E →+* E) A) = A := fun A =>
    Matrix.ext fun i j => hσ _
  have yx : Formalism.UG.cT (σ : E →+* E) Y * J * X = 1 := by
    have := congrArg (Formalism.UG.cT (σ : E →+* E)) xy
    rwa [Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, Formalism.UG.cT_one, ← Matrix.mul_assoc] at this
  set φ := inclR (F := F) (E := E) (AF F)
  have m1 : ∀ {L : Matrix (Fin r) (Fin n) E} {C : Matrix (Fin n) (Fin r) E}, L * C = 1 → L.map φ * C.map φ = 1 :=
    fun h => by rw [← Matrix.map_mul, h, Matrix.map_one _ (map_zero _) (map_one _)]
  have h1 : ∑ a, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) a = 1 := by
    rw [Fintype.sum_option]
    exact sub_add_cancel _ _
  have cs : ∀ j : Fin r, Formalism.UG.cT (σ : E →+* E) (single j j (1 : E)) = single j j (1 : E) := fun j => by
    rw [Formalism.UG.cT, Matrix.map_single, transpose_single, map_one]
  have eY : ∀ j, fam (adjA σ J) (idemA (F := F) X (Formalism.UG.cT (σ : E →+* E) Y * J)) (some (.inr j)) =
      Y.map φ * single j j (1 : AF F ⊗[F] E) * (Formalism.UG.cT (σ : E →+* E) X * J).map φ := fun j => by
    rw [← idemA_eq]
    change adjA σ J (idemA X _ j) = _
    rw [idemA, idemA, adjA_map, Formalism.UG.cT_mul, Formalism.UG.cT_mul, Formalism.UG.cT_mul, cc, cT_form hJ, cs]
    simp only [Matrix.mul_assoc]
    rw [Matrix.nonsing_inv_mul_cancel_left _ _ (det_isUnit hJ)]
  have kX : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * X.map φ = X.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 yx) (fun j => some (.inl j))
      (fun j => idemA_eq _ _ j)
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · exact ⟨i, rfl⟩
        · have := hd j; have := hd i; simp [wt] at h; omega)
      (fun i j h => by simp [wt]; omega) hz
  have kY : ∀ {z}, _ → ∃ B : Matrix (Fin r) (Fin r) (AF F ⊗[F] E), B.BlockTriangular d ∧ z * Y.map φ = Y.map φ * B :=
    fun hz => exists_blockTriangular_of_keeps_weights (w := wt d M) h1 (m1 xy) (fun j => some (.inr j)) eY
      (by
        rintro (_ | i | i) j h
        · have := hd j; simp [wt] at h; omega
        · have := hd j; have := hd i; simp [wt] at h; omega
        · exact ⟨i, rfl⟩)
      (fun i j h => by simp [wt]; omega) hz
  exact ⟨⟨kX hg, kX hg'⟩, kY hg, kY hg'⟩

end GlobalTheory.UAut
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemNilRad
section
noncomputable section

open Matrix
open scoped ContDiff

namespace GlobalTheory.TorFin

variable {n : ℕ} {G : Type} [Group G]

def IsUni (J u : Matrix (Fin n) (Fin n) ℂ) : Prop := uᴴ * J * u = J

def IsSkew (J Z : Matrix (Fin n) (Fin n) ℂ) : Prop := Zᴴ * J + J * Z = 0

def IsMulOn (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Prop :=
  ∀ a b, IsUni J a → IsUni J b → s (a * b) = s a * s b

def lineOf (s : Matrix (Fin n) (Fin n) ℂ → G) (Z : Matrix (Fin n) (Fin n) ℂ) (t : ℝ) : G := s (NormedSpace.exp (t • Z))

def smLoc (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) : Submodule ℂ (G → ℂ) where
  carrier := {f | ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
    ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod)}
  add_mem' := fun hf hf' k Z hZ g => (hf k Z hZ g).add (hf' k Z hZ g)
  zero_mem' := fun _ _ _ _ => contDiff_const
  smul_mem' := fun c _ hf k Z hZ g => (hf k Z hZ g).const_smul c

theorem mem_smLoc {J : Matrix (Fin n) (Fin n) ℂ} {s : Matrix (Fin n) (Fin n) ℂ → G} {f : G → ℂ} :
    f ∈ smLoc J s ↔ ∀ (k : ℕ) (Z : Fin k → Matrix (Fin n) (Fin n) ℂ), (∀ i, IsSkew J (Z i)) → ∀ g,
      ContDiff ℝ ∞ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => lineOf s (Z i) (t i)).prod) := Iff.rfl

example (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G) (a : ℂ) : (fun _ => a) ∈ smLoc J s :=
  fun _ _ _ _ => contDiff_const

def IsLieRep {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) : Prop :=
  ∀ X Y, ρ (X * Y - Y * X) = ρ X * ρ Y - ρ Y * ρ X

example : IsLieRep (LinearMap.id : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Matrix (Fin n) (Fin n) ℂ) := fun _ _ => rfl

def IsRightDer (J : Matrix (Fin n) (Fin n) ℂ) (s : Matrix (Fin n) (Fin n) ℂ → G)
    (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] Module.End ℂ (smLoc J s)) : Prop :=
  ∀ Z, IsSkew J Z → ∀ (f : smLoc J s) (g : G) (t : ℝ),
    HasDerivAt (fun τ : ℝ => f.1 (g * lineOf s Z τ)) ((ρ Z f).1 (g * lineOf s Z t)) t

def rder (γ : ℝ → G) (φ : G → ℂ) : G → ℂ := fun g => deriv (fun t => φ (g * γ t)) 0

def wop (z : List (ℝ → G) →₀ ℂ) (f : G → ℂ) : G → ℂ := fun g => z.sum fun l c => c * l.foldr rder f g

def invAlg {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) : Subalgebra ℂ A :=
  Algebra.adjoin ℂ (Set.range ρ) ⊓ Subalgebra.centralizer ℂ
    {r | ∃ g g' : Matrix (Fin n) (Fin n) ℂ, g * g' = 1 ∧ ∀ Y, r * ρ Y = ρ (g * Y * g') * r}

theorem mem_invAlg {A : Type} [Ring A] [Algebra ℂ A] {ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A} {T : A} :
    T ∈ invAlg ρ ↔ T ∈ Algebra.adjoin ℂ (Set.range ρ) ∧ ∀ r, ∀ g g' : Matrix (Fin n) (Fin n) ℂ, g * g' = 1 →
      (∀ Y, r * ρ Y = ρ (g * Y * g') * r) → r * T = T * r :=
  ⟨fun h => ⟨h.1, fun r g g' h1 h2 => h.2 r ⟨g, g', h1, h2⟩⟩, fun h => ⟨h.1, fun r ⟨g, g', h1, h2⟩ => h.2 r g g' h1 h2⟩⟩

def leftIdl {A : Type} [Ring A] [Algebra ℂ A] (ρ : Matrix (Fin n) (Fin n) ℂ →ₗ[ℂ] A) (𝔫 : Set (Matrix (Fin n) (Fin n) ℂ)) :
    Submodule ℂ A :=
  Submodule.span ℂ {a | ∃ Y ∈ 𝔫, ∃ w ∈ Algebra.adjoin ℂ (Set.range ρ), a = ρ Y * w}

def IsIntMod {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) (H : A) : Prop :=
  ∃ N : ℕ, H ^ N ∈ I ⊔ Submodule.span ℂ {a | ∃ k < N, ∃ z ∈ Z, a = H ^ k * z}

example {A : Type} [Ring A] [Algebra ℂ A] (Z : Subalgebra ℂ A) (I : Submodule ℂ A) {H : A} (h : H ∈ Z) : IsIntMod Z I H :=
  ⟨1, Submodule.mem_sup_right (Submodule.subset_span ⟨0, one_pos, H, h, by simp⟩)⟩

def nilRad (J : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) : Submodule ℂ (Matrix (Fin n) (Fin n) ℂ) where
  carrier := {Y | Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x}
  add_mem' := fun {Y Y'} h h' => ⟨by rw [add_mulVec, h.1, h'.1, add_zero], by rw [vecMul_add, h.2.1, h'.2.1, add_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; let ⟨a', e'⟩ := h'.2.2 v hv; ⟨a + a', by rw [add_mulVec, e, e', add_smul]⟩⟩
  zero_mem' := ⟨zero_mulVec _, vecMul_zero _, fun v _ => ⟨0, by simp⟩⟩
  smul_mem' := fun c Y h => ⟨by rw [smul_mulVec, h.1, smul_zero], by rw [vecMul_smul, h.2.1, smul_zero],
    fun v hv => let ⟨a, e⟩ := h.2.2 v hv; ⟨c * a, by rw [smul_mulVec, e, smul_smul]⟩⟩

theorem mem_nilRad {J Y : Matrix (Fin n) (Fin n) ℂ} {x : Fin n → ℂ} : Y ∈ nilRad J x ↔
    Y *ᵥ x = 0 ∧ (star x ᵥ* J) ᵥ* Y = 0 ∧ ∀ v, (star x ᵥ* J) ⬝ᵥ v = 0 → ∃ a : ℂ, Y *ᵥ v = a • x := Iff.rfl

def projL (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : Matrix (Fin n) (Fin n) ℂ := vecMulVec x (star y ᵥ* J)

def torMat (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) (z : ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  1 + (z - 1) • projL J x y + ((star z)⁻¹ - 1) • projL J y x

example (J : Matrix (Fin n) (Fin n) ℂ) (x y : Fin n → ℂ) : torMat J x y 1 = 1 := by simp [torMat]

end GlobalTheory.TorFin

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSupportWordMul
section
noncomputable section

open GlobalTheory.AdelicU GlobalTheory.SiegelSet

namespace GlobalTheory.UAut

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

def wordMul (w z : List (ℝ → GAd σ J) →₀ ℂ) : List (ℝ → GAd σ J) →₀ ℂ :=
  w.sum fun l a => z.sum fun l' b => Finsupp.single (l ++ l') (a * b)

theorem dop_add_comb (z z' : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : dop (z + z') f = dop z f + dop z' f := by
  funext g
  exact Finsupp.sum_add_index' (fun _ => zero_mul _) (fun _ _ _ => add_mul _ _ _)

theorem dop_smul_comb (c : ℂ) (z : List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) : dop (c • z) f = c • dop z f := by
  funext g
  simp only [dop, Pi.smul_apply, smul_eq_mul]
  rw [Finsupp.sum_smul_index (fun _ => zero_mul _), Finsupp.mul_sum]
  simp only [smul_eq_mul, mul_assoc]

theorem dop_zero_comb (f : GAd σ J → ℂ) : dop (0 : List (ℝ → GAd σ J) →₀ ℂ) f = 0 := by
  funext g
  simp [dop]

theorem dop_single (l : List (ℝ → GAd σ J)) (c : ℂ) (f : GAd σ J → ℂ) :
    dop (Finsupp.single l c) f = fun g => c * l.foldr lineDer f g := by
  funext g
  simp [dop, Finsupp.sum_single_index]

theorem dop_sum_comb {ι : Type} (s : Finset ι) (z : ι → List (ℝ → GAd σ J) →₀ ℂ) (f : GAd σ J → ℂ) :
    dop (∑ i ∈ s, z i) f = ∑ i ∈ s, dop (z i) f := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [dop_zero_comb]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, dop_add_comb, ih]

theorem mem_support_wordMul {w z : List (ℝ → GAd σ J) →₀ ℂ} {m : List (ℝ → GAd σ J)} (hm : m ∈ (wordMul w z).support) :
    ∃ l ∈ w.support, ∃ l' ∈ z.support, m = l ++ l' := by
  classical
  obtain ⟨l, hl, h1⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum hm)
  obtain ⟨l', hl', h2⟩ := Finset.mem_biUnion.1 (Finsupp.support_sum h1)
  exact ⟨l, hl, l', hl', Finset.mem_singleton.1 (Finsupp.support_single_subset h2)⟩

theorem IsCentral.zero : IsCentral σ J (0 : List (ℝ → GAd σ J) →₀ ℂ) :=
  ⟨by simp, fun f _ a _ g => by simp [dop_zero_comb]⟩

theorem IsCentral.add {z z' : List (ℝ → GAd σ J) →₀ ℂ} (h : IsCentral σ J z) (h' : IsCentral σ J z') :
    IsCentral σ J (z + z') := by
  classical
  refine ⟨fun l hl γ hγ => ?_, fun f hf a ha g => ?_⟩
  · rcases Finset.mem_union.1 (Finsupp.support_add hl) with hl | hl
    exacts [h.1 l hl γ hγ, h'.1 l hl γ hγ]
  · simp only [dop_add_comb, Pi.add_apply, h.2 f hf a ha g, h'.2 f hf a ha g]

theorem IsCentral.smul {z : List (ℝ → GAd σ J) →₀ ℂ} (h : IsCentral σ J z) (c : ℂ) : IsCentral σ J (c • z) :=
  ⟨fun l hl γ hγ => h.1 l (Finsupp.support_smul hl) γ hγ, fun f hf a ha g => by
    simp only [dop_smul_comb, Pi.smul_apply, h.2 f hf a ha g]⟩

end GlobalTheory.UAut

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemTwistedCentralizerRestrictedProductIff
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.EulerAbs

theorem mem_twCent_iff_forall_comp : ∀ {X V : Type} {Y : V → Type} [Group X] [TopologicalSpace X] [∀ v, Group (Y v)] [∀ v, TopologicalSpace (Y v)] (pf : ∀ v, X →* Y v) (K : ∀ v, Subgroup (Y v)), GlobalTheory.RestrMeas.IsRestrGroup (GlobalTheory.RestrMeas.noArch X) pf K → ∀ (θ : X →* X) (θv : ∀ v, Y v →* Y v), (∀ v x, pf v (θ x) = θv v (pf v x)) → ∀ (δ x : X), x ∈ twCent θ δ ↔ ∀ v, pf v x ∈ twCent (θv v) (pf v δ) := by
  intro X V Y _ _ _ _ pf K hX θ θv hθ δ x
  simp only [twCent, Subgroup.mem_mk, Set.mem_setOf_eq]
  constructor
  · intro h v
    have := congrArg (pf v) h
    simpa [map_mul, hθ] using this
  · intro h
    apply hX.ext
    · intro w; exact isEmptyElim w
    · intro v
      simpa [map_mul, hθ] using h v

end GlobalTheory.EulerAbs
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIffStatement
section
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_weylCellUnitaryGroup_longSimpleReflection_iff : ∀ (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (σ : L →+* L) (n : ℕ)
    (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 → Even n → ∀ (y : GU σ n),
    IsWeylRep (simpleU k) (y : GL (Fin n) L) → ∀ (u : GU σ n),
    u ∈ cellU y ↔ ∀ i j, ¬ (i = lo k ∧ j = (lo k).rev) →
      ((u : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) i j = (1 : Matrix (Fin n) (Fin n) L) i j := by
  first | exact @GlobalTheory.cellU_rankOne_shape | exact GlobalTheory.cellU_rankOne_shape | (intros; apply GlobalTheory.cellU_rankOne_shape <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.ModulusLeviMaximalCompactOne
section
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.DeltaOneKGL

theorem deltaHalf_KGL_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (a b : ℕ) (w : Pl E) (m : GLw a w × GLw b w), m.1 ∈ GlobalTheory.LFun.KGL w a → m.2 ∈ GlobalTheory.LFun.KGL w b → GlobalTheory.SmGL.deltaHalf (w.adicCompletion E) (GlobalTheory.SmGL.Two (Fin a) (Fin b)) (GlobalTheory.SmGL.leviTwo (w.adicCompletion E) (Fin a) (Fin b) m) = 1 := by
  intro E _ _ _ a b w m h1 h2
  haveI : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
    Valuation.Compatible.ofValuation _
  have he := ValuativeRel.isEquiv (ValuativeRel.valuation (w.adicCompletion E))
    (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))
  have hn : ∀ {n : ℕ} (k : GLw n w), k ∈ GlobalTheory.LFun.KGL w n →
      GlobalTheory.SplitWeil.nabs (w.adicCompletion E) (Matrix.GeneralLinearGroup.det k) = 1 := by
    intro n k hk
    apply GlobalTheory.SmGL.nabs_eq_one
    rw [he.eq_one_iff_eq_one]
    exact GlobalTheory.BCT.AbsHalfInv.v_det_KGL hk
  rw [GlobalTheory.SmGL.deltaHalf_two]
  ext
  simp [GlobalTheory.SmGL.val_absPow, hn _ h1, hn _ h2]

end GlobalTheory.DeltaOneKGL
end

