import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0009
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0008
import Development.EtaleCohomology.TateTwists.Bundle0003
import Development.EtaleCohomology.TateTwists.Bundle0002
import Development.EtaleCohomology.TateTwists.Bundle0004

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSheafShortComplexExactIffLocalLiftsHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ExactIffPf

variable {R : Type} [CommRing R]

theorem inj_of_mono {F G : Shv R} (φ : F ⟶ G) [Mono φ] (U : Scheme.{0}) :
    Function.Injective (Sec.map φ (U := U)) := by
  have : Mono φ.hom := inferInstance
  have : Mono (φ.hom.app (op U)) := inferInstance
  exact (ModuleCat.mono_iff_injective _).1 this

theorem ker_sec {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) (b : Sec F U) (hb : Sec.map φ b = 0) :
    ∃ k : Sec (kernel φ) U, Sec.map (kernel.ι φ) k = b := by
  let E := sheafToPresheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R)) ⋙
    (evaluation _ _).obj (op U)
  have hl : IsLimit (Fork.ofι (E.map (kernel.ι φ))
      (by rw [← Functor.map_comp, kernel.condition, Functor.map_zero, comp_zero]) :
      Fork (E.map φ) 0) := isLimitOfHasKernelOfPreservesLimit E φ
  let M := LinearMap.ker (φ.hom.app (op U)).hom
  let s : ModuleCat.of (ULift.{1} R) M ⟶ E.obj F := ModuleCat.ofHom M.subtype
  have hs : s ≫ E.map φ = s ≫ 0 := by
    ext x
    simp [s, E]
  obtain ⟨l, hl'⟩ := Fork.IsLimit.lift' hl s hs
  refine ⟨l.hom ⟨b, hb⟩, ?_⟩
  have := congrArg (fun m => m.hom (⟨b, hb⟩ : M)) hl'
  simpa [s, E] using this

theorem exact_iff (S : ShortComplex (Shv R)) : S.Exact ↔ ∀ U (b : Sec S.X₂ U), Sec.map S.g b = 0 →
    Loc U fun V g => ∃ a : Sec S.X₁ V, Sec.map S.f a = Sec.res g b := by
  rw [S.exact_iff_epi_kernel_lift, ← Sheaf.isLocallySurjective_iff_epi' (φ := kernel.lift S.g S.f S.zero)]
  set φ := kernel.lift S.g S.f S.zero with hφ
  have hfac : ∀ V (a : Sec S.X₁ V), Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map S.f a := by
    intro V a
    show ((φ ≫ kernel.ι S.g).hom.app (op V)).hom a = _
    rw [hφ, kernel.lift_ι]
  have hnat : ∀ {V U : Scheme.{0}} (g : V ⟶ U) (k : Sec (kernel S.g) U),
      Sec.map (kernel.ι S.g) (Sec.res g k) = Sec.res g (Sec.map (kernel.ι S.g) k) := by
    intro V U g k
    have := congrArg (fun m => m.hom k) ((kernel.ι S.g).hom.naturality g.op)
    simp [Sec.map, Sec.res] at this ⊢
  constructor
  · intro h U b hb
    obtain ⟨k, rfl⟩ := ker_sec S.g U b hb
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology.{0} φ.hom k, ?_⟩
    rintro V g ⟨t, ht⟩
    refine ⟨t, ?_⟩
    rw [← hfac]
    rw [show Sec.map φ t = Sec.res g k from ht, hnat]
  · intro h
    constructor
    intro U k
    obtain ⟨T, hT, hTk⟩ := h U (Sec.map (kernel.ι S.g) k) (by
      show ((kernel.ι S.g ≫ S.g).hom.app (op U)).hom k = 0
      rw [kernel.condition]; rfl)
    refine Scheme.etaleTopology.superset_covering ?_ hT
    intro V g hg
    obtain ⟨a, ha⟩ := hTk V g hg
    refine ⟨a, ?_⟩
    apply inj_of_mono (kernel.ι S.g) V
    change Sec.map (kernel.ι S.g) (Sec.map φ a) = Sec.map (kernel.ι S.g) (Sec.res g k)
    rw [hfac, hnat, ha]

end LateralTheory.EtaleFoundations.ExactIffPf

theorem LateralTheory.EtaleFoundations.etale_sheaf_short_complex_exact_iff_local_lifts_holds : LateralTheory.EtaleFoundations.EtaleSheafShortComplexExactIffLocallyLifts := by
  intro R _ S
  exact LateralTheory.EtaleFoundations.ExactIffPf.exact_iff S
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialChainsBasicPropertiesHold
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ChainsBasicPf

variable (R : Type) [CommRing R]

lemma chainsN_d (E : Spc) (p : ℕ) :
    ((chainsN R).obj E).d (p + 1) p = ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • (free R).map (E.δ i) :=
  AlgebraicTopology.AlternatingFaceMapComplex.obj_d_eq _ p

lemma chains_map_f {E E' : Spc} (f : E ⟶ E') (p : ℕ) :
    ((chains R).map f).f (-(p : ℤ)) =
      (chainsXIso R E p).hom ≫ (free R).map (f.app (op (SimplexCategory.mk p))) ≫ (chainsXIso R E' p).inv :=
  HomologicalComplex.extendMap_f _ _ rfl

lemma chains_d (E : Spc) (p : ℕ) :
    ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) =
      (chainsXIso R E (p + 1)).hom ≫ ((chainsN R).obj E).d (p + 1) p ≫ (chainsXIso R E p).inv :=
  HomologicalComplex.extend_d_eq _ _ rfl rfl

lemma chains_d' (E : Spc) (p : ℕ) :
    (chainsXIso R E (p + 1)).inv ≫ ((chains R).obj E).d (-((p + 1 : ℕ) : ℤ)) (-(p : ℤ)) ≫ (chainsXIso R E p).hom =
      ((chainsN R).obj E).d (p + 1) p := by
  rw [chains_d R E p]
  simp only [Category.assoc, Iso.inv_hom_id_assoc]
  erw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

lemma chains_le (E : Spc) : ((chains R).obj E).IsStrictlyLE 0 :=
  inferInstanceAs (CochainComplex.IsStrictlyLE (((chainsN R).obj E).extend ComplexShape.embeddingDownNat) 0)

end LateralTheory.EtaleFoundations.ChainsBasicPf

open LateralTheory.EtaleFoundations.ChainsBasicPf in
theorem LateralTheory.EtaleFoundations.etale_simplicial_chains_basic_properties_hold : LateralTheory.EtaleFoundations.EtaleSimplicialChainsFreeDescription := by
  intro R _
  refine ⟨fun E => chains_le R E, fun {E E'} f p => ?_, fun E p => ?_⟩
  · rw [chains_map_f R f p]
    simp only [Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [chains_d' R E p]
    exact chainsN_d R E p
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainExistsFromNaturalSections
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def EtaleSimplicialCochainExistsFromNaturalSections : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ} (a : ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx E p U → Sec (I.X s) U), (∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (a p s h U x) = a p s h V (x.res g)) → ∃ α : Cochain ((chains R).obj E) I n, ∀ p s h U x, ev α p s h U x = a p s h U x

def EtaleSimplicialCochainEvaluationDifferentialFormula : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n m : ℤ} (hm : n + 1 = m) (α : Cochain ((chains R).obj E) I n) (U : Scheme.{0}), (∀ (x : Sx E 0 U), ev (δ n m α) 0 m (by simp) U x = Sec.map (I.d n m) (ev α 0 n (by simp) U x)) ∧ ∀ (p : ℕ) (s t : ℤ) (hs : -((p + 1 : ℕ) : ℤ) + n = s) (ht : -((p + 1 : ℕ) : ℤ) + m = t) (x : Sx E (p + 1) U), ev (δ n m α) (p + 1) t ht U x = Sec.map (I.d s t) (ev α (p + 1) s hs U x) + m.negOnePow • ∑ i : Fin (p + 2), (-1 : ℤ) ^ (i : ℕ) • ev α p t (by omega) U (x.face i)

def EtaleSimplicialCochainEvaluationProperties : Prop := ∀ (R : Type) [CommRing R] {E : Spc} {I : Cx R} {n : ℤ}, (∀ (α β : Cochain ((chains R).obj E) I n) p s h U x, ev (α + β) p s h U x = ev α p s h U x + ev β p s h U x ∧ ev (α - β) p s h U x = ev α p s h U x - ev β p s h U x ∧ ev (0 : Cochain ((chains R).obj E) I n) p s h U x = 0 ∧ ∀ c : ℤ, ev (c • α) p s h U x = c • ev α p s h U x) ∧ (∀ (α : Cochain ((chains R).obj E) I n) p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx E p U), Sec.res g (ev α p s h U x) = ev α p s h V (x.res g)) ∧ (∀ α β : Cochain ((chains R).obj E) I n, (∀ p s h U x, ev α p s h U x = ev β p s h U x) → α = β) ∧ (∀ {E' : Spc} (f : E' ⟶ E) (α : Cochain ((chains R).obj E) I n) p s h U (x : Sx E' p U), ev ((Cochain.ofHom ((chains R).map f)).comp α (zero_add n)) p s h U x = ev α p s h U (x.map f)) ∧ ∀ {J : Cx R} (m : I ⟶ J) (α : Cochain ((chains R).obj E) I n) p s h U x, ev (α.comp (Cochain.ofHom m) (add_zero n)) p s h U x = Sec.map (m.f s) (ev α p s h U x)

def EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary : Prop := ∀ (R : Type) [CommRing R] (X : Scheme.{0}) (I : Cx R) (m n : ℤ), m + 1 = n → ∀ α : Cocycle ((chains R).obj (sch.obj X)) I n, ev α.1 0 n (by simp) X (𝟙 X) = 0 → ∃ β : Cochain ((chains R).obj (sch.obj X)) I m, δ m n β = α.1

def a0 {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ (p : ℕ) (s : ℤ), -(p : ℤ) + n = s → ∀ U : Scheme.{0}, Sx (sch.obj X) p U → Sec (I.X s) U
  | 0, s, h, U, x => (show n = s by omega) ▸ Sec.res (x : U ⟶ X) z
  | _ + 1, _, _, _, _ => 0

lemma etaleSimplicialCochain_scheme_section_extension_degree_zero {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) (h : -((0:ℕ) : ℤ) + n = n)
    (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U) : a0 X I n z 0 n h U x = Sec.res (x : U ⟶ X) z := rfl

lemma res_res {R : Type} [CommRing R] {F : Shv R} {W V U : Scheme.{0}} (g : W ⟶ V) (f : V ⟶ U) (z : Sec F U) :
    Sec.res g (Sec.res f z) = Sec.res (g ≫ f) z := by
  simp [Sec.res, op_comp, Functor.map_comp]

lemma res_id {R : Type} [CommRing R] {F : Shv R} {U : Scheme.{0}} (z : Sec F U) : Sec.res (𝟙 U) z = z := by
  simp [Sec.res]

lemma map_res {R : Type} [CommRing R] {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (z : Sec F U) :
    Sec.map φ (Sec.res g z) = Sec.res g (Sec.map φ z) := by
  simp only [Sec.map, Sec.res]
  exact congrArg (fun f => ModuleCat.Hom.hom f z) (φ.hom.naturality g.op)

lemma etaleSimplicialCochain_scheme_section_extension_naturality {R : Type} [CommRing R] (X : Scheme.{0}) (I : Cx R) (n : ℤ) (z : Sec (I.X n) X) :
    ∀ p s h (V U : Scheme.{0}) (g : V ⟶ U) (x : Sx (sch.obj X) p U),
      Sec.res g (a0 X I n z p s h U x) = a0 X I n z p s h V (x.res g) := by
  intro p s h V U g x
  cases p with
  | zero =>
    obtain rfl : s = n := by omega
    exact res_res g x z
  | succ q => simp [a0, Sec.res]

end LateralTheory.EtaleFoundations

open LateralTheory.EtaleFoundations in
theorem LateralTheory.EtaleFoundations.etaleSimplicialCochain_scheme_class_of_evaluation_properties (hmk : EtaleSimplicialCochainExistsFromNaturalSections) (hdl : EtaleSimplicialCochainEvaluationDifferentialFormula)
    (hb : EtaleSimplicialCochainEvaluationProperties) (hcob : EtaleSimplicialSchemeCocycleVanishingAtIdIsCoboundary) : EtaleSchemeGlobalSectionCohomologyClass := by
  intro R _ X I m n k hmn hnk

  have v0 : ∀ {q : ℤ} (β : Cochain ((chains R).obj (sch.obj X)) I q) (U : Scheme.{0}) (x : Sx (sch.obj X) 0 U),
      ev β 0 q (by simp) U x = Sec.res (x : U ⟶ X) (ev β 0 q (by simp) X (𝟙 X)) := by
    intro q β U x
    rw [(hb R).2.1 β 0 q (by simp) U X x (𝟙 X)]
    rfl
  refine ⟨?_, ?_⟩
  · intro z hz
    obtain ⟨α, hα⟩ := hmk R (a0 X I n z) (etaleSimplicialCochain_scheme_section_extension_naturality X I n z)
    have hδ : δ n k α = 0 := by
      apply (hb R).2.2.1
      intro p s h U x
      rw [((hb R).1 (δ n k α) (δ n k α) p s h U x).2.2.1]
      cases p with
      | zero =>
        obtain rfl : s = k := by omega
        rw [(hdl R hnk α U).1 x, hα, etaleSimplicialCochain_scheme_section_extension_degree_zero]
        exact (map_res (I.d n s) (x : U ⟶ X) z).trans (by rw [hz]; simp [Sec.res])
      | succ p =>
        rw [(hdl R hnk α U).2 p (-((p + 1 : ℕ) : ℤ) + n) s rfl h x]
        simp only [hα]
        cases p with
        | zero =>
          obtain rfl : s = n := by omega
          simp [a0, Fin.sum_univ_two]
          rw [show x.face 0 = x from rfl, show x.face 1 = x from rfl]
          exact add_neg_cancel _
        | succ p => simp [a0]
    refine ⟨Cocycle.mk α k hnk hδ, ?_, ?_⟩
    · intro U x; exact hα 0 n (by simp) U x
    · intro p s h U x; rw [show (Cocycle.mk α k hnk hδ).1 = α from rfl, hα]; rfl
  · intro α
    have hd0 : Sec.map (I.d n k) (ev α.1 0 n (by simp) X (𝟙 X)) = 0 := by
      rw [← (hdl R hnk α.1 X).1 (𝟙 X), Cocycle.δ_eq_zero]
      exact ((hb R (E := sch.obj X) (I := I) (n := k)).1 0 0 0 k (by simp) X (𝟙 X)).2.2.1
    refine ⟨hd0, ?_⟩
    rw [CohomologyClass.mk_eq_zero_iff, mem_coboundaries_iff α m hmn]
    constructor
    · rintro ⟨β, hβ⟩
      refine ⟨ev β 0 m (by simp) X (𝟙 X), ?_⟩
      rw [← (hdl R hmn β X).1 (𝟙 X), hβ]
    · rintro ⟨y, hy⟩
      obtain ⟨γ, hγ⟩ := hmk R (a0 X I m y) (etaleSimplicialCochain_scheme_section_extension_naturality X I m y)
      have hc : δ n k (α.1 - δ m n γ) = 0 := by
        rw [δ_sub, Cocycle.δ_eq_zero, δ_δ, sub_zero]
      obtain ⟨β, hβ⟩ := hcob R X I m n hmn (Cocycle.mk (α.1 - δ m n γ) k hnk hc) (by
        have e := ((hb R).1 (α : Cochain ((chains R).obj (sch.obj X)) I n) (δ m n γ) 0 n (by simp) X (𝟙 X)).2.1
        have e2 : ev (δ m n γ) 0 n (by simp) X (𝟙 X) = Sec.map (I.d m n) y := by
          rw [(hdl R hmn γ X).1 (𝟙 X)]
          exact congrArg (Sec.map (I.d m n)) ((hγ 0 m (by simp) X (𝟙 X)).trans (res_id y))
        exact e.trans ((congrArg (ev (α : Cochain ((chains R).obj (sch.obj X)) I n) 0 n (by simp) X (𝟙 X) - ·) e2).trans
          (sub_eq_zero.mpr hy.symm)))
      refine ⟨β + γ, ?_⟩
      rw [δ_add, hβ]
      show α.1 - δ m n γ + δ m n γ = α.1
      abel
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleSimplicialCochainShortExactSequenceHolds
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

theorem LateralTheory.EtaleFoundations.etale_simplicial_cochain_short_exact_sequence_holds : LateralTheory.EtaleFoundations.EtaleCochainsInjectiveShortExact := by
  intro R _ I hI S hS n
  have hd := (HomologicalComplex.shortExact_iff_degreewise_shortExact S).1 hS
  have hv : ∀ {Y : Cx R} (φ : S.X₁ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hv2 : ∀ {Y : Cx R} (φ : S.X₂ ⟶ Y) (z : Cochain Y I n) (p q : ℤ) (hpq : p + n = q),
      ((Cochain.ofHom φ).comp z (zero_add n)).v p q hpq = φ.f p ≫ z.v p q hpq := by
    intro Y φ z p q hpq
    rw [Cochain.zero_cochain_comp_v, Cochain.ofHom_v]
  have hm : ∀ p, Mono (S.f.f p) := fun p => (hd p).mono_f
  have he : ∀ p, Epi (S.g.f p) := fun p => (hd p).epi_g
  refine ⟨?_, ?_, ?_⟩
  · intro a
    refine ⟨Cochain.mk (fun p q h => haveI := hm p; haveI := hI q
      Injective.factorThru (a.v p q h) (S.f.f p)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv, Cochain.mk_v]
    have := hm p; have := hI q
    exact Injective.comp_factorThru _ _
  · intro b hb
    refine ⟨Cochain.mk (fun p q h => haveI := (hd p).epi_g
      (hd p).exact.desc (b.v p q h) (by
        have := congrArg (fun z => z.v p q h) hb
        simp only [hv] at this; exact this)), ?_⟩
    apply Cochain.ext
    intro p q hpq
    rw [hv2]
    haveI := (hd p).epi_g
    exact (hd p).exact.g_desc _ _
  · intro c hc
    apply Cochain.ext
    intro p q hpq
    have := congrArg (fun z => z.v p q hpq) hc
    simp only [hv2, Cochain.zero_v] at this
    have hep := he p
    rw [Cochain.zero_v]
    exact (cancel_epi (S.g.f p)).1 (by simpa using this)
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistCupPairingOfTensorAndResolutionPro
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations

def twpair_tens_ex : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R) (τ : Pair I J K), τ.IsTensor

def twpair_tens_univ : Prop :=
  ∀ (R : Type) [CommRing R] {I J K : Cx R} (τ : Pair I J K), τ.IsTensor → (∀ {I' J' K' : Cx R} (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J'), ∃! u : K ⟶ K', τ.Compat ν f g u) ∧ (I.IsStrictlyGE 0 → J.IsStrictlyGE 0 → K.IsStrictlyGE 0) ∧ ∀ {K' : Cx R} (u : K ⟶ K'), ∃ ν : Pair I J K', τ.Compat ν (𝟙 I) (𝟙 J) u

def twpair_tens_twres : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ), i + j = k → ∀ {I J T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (I.X 0) U) (e' : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (J.X 0) U), IsTwRes q i I e → IsTwRes q j J e' → (∀ t, FlatS (J.X t)) → ∀ τ : Pair I J T, τ.IsTensor → IsTwRes q k T fun U ζ => τ.mul U 0 0 0 (add_zero 0) (e U ζ) (e' U ζ)

def twpair_twres_ext : Prop :=
  ∀ (q : ℕ) [NeZero q] (i : ℤ), IsTwRes q i (res _ (tw q i)) (fun _ ζ => resGen i ζ) ∧ (∀ t, FlatS ((res _ (tw q i)).X t)) ∧ ∀ {T : Cx (ZMod q)} (e : ∀ U : Scheme.{0}, Prim q Γ(U, ⊤) → Sec (T.X 0) U), IsTwRes q i T e → (∃ u : T ⟶ res _ (tw q i), ∀ U ζ, Sec.map (u.f 0) (e U ζ) = resGen i ζ) ∧ ∀ u u' : T ⟶ res _ (tw q i), (∀ U ζ, Sec.map (u.f 0) (e U ζ) = Sec.map (u'.f 0) (e U ζ)) → Nonempty (Homotopy u u')

def twpair_cup_compat : Prop :=
  ∀ (R : Type) [CommRing R] {I J K I' J' K' : Cx R} (μ : Pair I J K) (ν : Pair I' J' K') (f : I ⟶ I') (g : J ⟶ J') (u : K ⟶ K'), μ.Compat ν f g u → ∀ (E : Spc) {n m k : ℤ} (hk : n + m = k) a b, cpush _ u k (μ.cup E hk a b) = ν.cup E hk (cpush _ f n a) (cpush _ g m b)

def twpair_zc_fun : Prop :=
  ∀ (R : Type) [CommRing R] , (∀ (K I : Cx R) (n : ℤ) x, cpull (𝟙 K) I n x = x ∧ cpush K (𝟙 I) n x = x) ∧ (∀ {K L M : Cx R} (f : K ⟶ L) (g : L ⟶ M) (I : Cx R) (n : ℤ) x, cpull (f ≫ g) I n x = cpull f I n (cpull g I n x)) ∧ (∀ (K : Cx R) {I J M : Cx R} (f : I ⟶ J) (g : J ⟶ M) (n : ℤ) x, cpush K (f ≫ g) n x = cpush K g n (cpush K f n x)) ∧ (∀ {K L I J : Cx R} (f : K ⟶ L) (g : I ⟶ J) (n : ℤ) x, cpull f J n (cpush L g n x) = cpush K g n (cpull f I n x)) ∧ (∀ {K L : Cx R} (f g : K ⟶ L), Nonempty (Homotopy f g) → ∀ (I : Cx R) (n : ℤ), cpull f I n = cpull g I n ∧ cpush I f n = cpush I g n)

theorem etale_tate_twist_cup_pairing_of_tensor_and_resolution_properties (h1 : twpair_tens_ex) (h2 : twpair_tens_univ) (h3 : twpair_tens_twres)
    (h4 : twpair_twres_ext) (h5 : twpair_cup_compat) (h6 : twpair_zc_fun) : LateralTheory.EtaleFoundations.EtaleTwistResolutionPairingCupUnique := by
  intro q _ i j
  obtain ⟨T, τ, hτ⟩ := h1 (ZMod q) (res _ (tw q i)) (res _ (tw q j))
  have hT := h3 q i j (i + j) rfl _ _ (h4 q i).1 (h4 q j).1 (h4 q j).2.1 τ hτ
  obtain ⟨⟨u, hu⟩, hhom⟩ := (h4 q (i + j)).2.2 _ hT
  refine ⟨?_, ?_⟩
  · obtain ⟨ν, hν⟩ := (h2 (ZMod q) τ hτ).2.2 u
    apply pick_spec
    refine ⟨ν, fun U ζ => ?_⟩
    have := hν U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)
    rw [← hu U ζ, this]
    rfl
  · intro k hk μ ν hμ hν E n m w h
    subst hk
    obtain ⟨uμ, huμ, -⟩ := (h2 (ZMod q) τ hτ).1 μ (𝟙 _) (𝟙 _)
    obtain ⟨uν, huν, -⟩ := (h2 (ZMod q) τ hτ).1 ν (𝟙 _) (𝟙 _)
    have hgen : ∀ U ζ, Sec.map (uμ.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) =
        Sec.map (uν.f 0) (τ.mul U 0 0 0 (add_zero 0) (resGen i ζ) (resGen j ζ)) := by
      intro U ζ
      rw [huμ U 0 0 0 (add_zero 0), huν U 0 0 0 (add_zero 0)]
      exact (hμ U ζ).trans (hν U ζ).symm
    have hh := hhom uμ uν hgen
    have hp := ((h6 (ZMod q)).2.2.2.2 uμ uν hh ((chains (ZMod q)).obj E) w).2
    have hid := (h6 (ZMod q)).1
    ext a b
    have e1 := h5 (ZMod q) τ μ (𝟙 _) (𝟙 _) uμ huμ E h a b
    have e2 := h5 (ZMod q) τ ν (𝟙 _) (𝟙 _) uν huν E h a b
    rw [(hid _ _ n a).2, (hid _ _ m b).2] at e1 e2
    rw [← e1, ← e2, hp]

end LateralTheory.EtaleFoundations
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTateTwistTensorIsoOfGeneratorMapIso
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

noncomputable section
namespace LateralTheory.EtaleFoundations.TwMulPf

variable {R : Type} [CommRing R]

theorem sec_res_map {F G : Shv R} (φ : F ⟶ G) {V U : Scheme.{0}} (g : V ⟶ U) (x : Sec F U) :
    Sec.res g (Sec.map φ x) = Sec.map φ (Sec.res g x) := by
  have := LinearMap.congr_fun (congrArg ModuleCat.Hom.hom (φ.hom.naturality g.op)) x
  simpa using this.symm

theorem sec_map_comp {F G H : Shv R} (φ : F ⟶ G) (ψ : G ⟶ H) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map ψ (Sec.map φ x) = Sec.map (φ ≫ ψ) x := by
  simp [Sec.map]

theorem sec_map_id {F : Shv R} {U : Scheme.{0}} (x : Sec F U) : Sec.map (𝟙 F) x = x := by
  simp [Sec.map]

theorem loc_mono {U : Scheme.{0}} {P Q : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hPQ : ∀ V g, P V g → Q V g) : Loc U Q := by
  obtain ⟨S, hS, hP⟩ := h
  exact ⟨S, hS, fun V g hg => hPQ V g (hP V g hg)⟩

def secL {F G : Shv R} (φ : F ⟶ G) (U : Scheme.{0}) : Sec F U →ₗ[ULift.{1} R] Sec G U :=
  (φ.hom.app (op U)).hom

def transp {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') : Pair I J K' where
  mul U s t w h := (μ.mul U s t w h).compr₂ (secL (ψ.hom.f w) U)
  nat g s t w h a b := by
    change Sec.res g (Sec.map (ψ.hom.f w) _) = Sec.map (ψ.hom.f w) _
    rw [sec_res_map, μ.nat]
  leibniz U s t w h a b := by
    change Sec.map (K'.d w (w + 1)) (Sec.map (ψ.hom.f w) _) =
      Sec.map (ψ.hom.f (w + 1)) _ + s.negOnePow • Sec.map (ψ.hom.f (w + 1)) _
    rw [sec_map_comp, ψ.hom.comm w (w + 1), ← sec_map_comp, μ.leibniz]
    simp only [Sec.map, map_add, map_zsmul_unit]

theorem transp_lift {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (U : Scheme.{0}) (w : ℤ)
    (x : Tens I J U w) : (transp μ ψ).lift U w x = Sec.map (ψ.hom.f w) (μ.lift U w x) := by
  classical
  change _ = secL (ψ.hom.f w) U (μ.lift U w x)
  rw [← LinearMap.comp_apply]
  congr 1
  refine DirectSum.linearMap_ext _ fun p => TensorProduct.ext' fun a b => ?_
  simp [Pair.lift, transp]

theorem transp_isTensor {I J K K' : Cx R} (μ : Pair I J K) (ψ : K ≅ K') (hμ : μ.IsTensor) :
    (transp μ ψ).IsTensor := by
  refine ⟨fun U w y => ?_, fun U w x hx => ?_⟩
  · refine loc_mono (hμ.1 U w (Sec.map (ψ.inv.f w) y)) fun V g ⟨x, hx⟩ => ⟨x, ?_⟩
    rw [transp_lift, hx, ← sec_res_map, sec_map_comp, ← HomologicalComplex.comp_f, ψ.inv_hom_id,
      HomologicalComplex.id_f, sec_map_id]
  · refine hμ.2 U w x ?_
    rw [transp_lift] at hx
    have := congrArg (Sec.map (ψ.inv.f w)) hx
    rw [sec_map_comp, ← HomologicalComplex.comp_f, ψ.hom_inv_id, HomologicalComplex.id_f, sec_map_id] at this
    rw [this]
    exact map_zero _

theorem sgl_map_f_zero {F G : Shv R} (φ : F ⟶ G) {U : Scheme.{0}} (x : Sec F U) :
    Sec.map (((CochainComplex.singleFunctor (Shv R) 0).map φ).f 0) (Sec.map (sglι F) x) =
      Sec.map (sglι G) (Sec.map φ x) := by
  rw [sec_map_comp, sec_map_comp]
  congr 1

end LateralTheory.EtaleFoundations.TwMulPf

open LateralTheory.EtaleFoundations.TwMulPf in

def LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j : ℤ), ∃ (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)), μ.IsTensor

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∃ φ : tw q k ⟶ T, ∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))

def LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso : Prop :=
  ∀ (q : ℕ) [NeZero q] (i j k : ℤ) (T : Shv (ZMod q)) (μ : Pair (sgl (tw q i)) (sgl (tw q j)) (sgl T)),
    μ.IsTensor → i + j = k → ∀ φ : tw q k ⟶ T, (∀ (U : Scheme.{0}) (ζ : Prim q Γ(U, ⊤)),
      Sec.map (sglι T) (Sec.map φ (twGen k ζ)) =
        μ.mul U 0 0 0 (add_zero 0) (Sec.map (sglι _) (twGen i ζ)) (Sec.map (sglι _) (twGen j ζ))) → IsIso φ

open LateralTheory.EtaleFoundations.TwMulPf in
theorem LateralTheory.EtaleFoundations.etale_tate_twist_tensor_iso_of_generator_map_iso (h1 : LateralTheory.EtaleFoundations.EtaleTateTwistTensorPairingExists)
    (h2 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapExists) (h3 : LateralTheory.EtaleFoundations.EtaleTateTwistGeneratorCompatibleMapIsIso) :
    LateralTheory.EtaleFoundations.EtaleTateTwistSingletonTensorGenMul := by
  intro q _ i j k hk
  obtain ⟨T, μ, hμ⟩ := h1 q i j
  obtain ⟨φ, hφ⟩ := h2 q i j k T μ hμ hk
  have := h3 q i j k T μ hμ hk φ hφ
  let ψ : sgl T ≅ sgl (tw q k) := (CochainComplex.singleFunctor (Shv (ZMod q)) 0).mapIso (asIso φ).symm
  refine ⟨transp μ ψ, transp_isTensor μ ψ hμ, fun U ζ => ?_⟩
  change Sec.map (ψ.hom.f 0) (μ.mul U 0 0 0 (add_zero 0) _ _) = _
  rw [← hφ U ζ]
  change Sec.map (((CochainComplex.singleFunctor (Shv (ZMod q)) 0).map (inv φ)).f 0) _ = _
  rw [sgl_map_f_zero, sec_map_comp, sec_map_comp, IsIso.hom_inv_id_assoc]
end
end

-- bundled from Development.EtaleCohomology.TateTwists.EtaleTensorComplexExistsOfSheafTensorComplex
section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC
open scoped TensorProduct DirectSum

noncomputable section

namespace LateralTheory.EtaleFoundations

def tensPure {R : Type} [CommRing R] {I J : Cx R} {U : Scheme.{0}} (s t w : ℤ) (h : s + t = w)
    (a : Sec (I.X s) U) (b : Sec (J.X t) U) : Tens I J U w :=
  DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
    (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩ (a ⊗ₜ b)

def EtaleSheafTensorComplexExists : Prop :=
  ∀ (R : Type) [CommRing R] (I J : Cx R), ∃ (K : Cx R)
    (φ : ∀ (U : Scheme.{0}) (w : ℤ), Tens I J U w →ₗ[ULift.{1} R] Sec (K.X w) U),
    (∀ {V U : Scheme.{0}} (g : V ⟶ U) (w : ℤ) (x : Tens I J U w),
      Sec.res g (φ U w x) = φ V w (Tens.res g w x)) ∧
    (∀ (U : Scheme.{0}) (s t w : ℤ) (h : s + t = w) (a : Sec (I.X s) U) (b : Sec (J.X t) U),
      Sec.map (K.d w (w + 1)) (φ U w (tensPure s t w h a b)) =
        φ U (w + 1) (tensPure (s + 1) t (w + 1) (by omega) (Sec.map (I.d s (s + 1)) a) b) +
        s.negOnePow • φ U (w + 1) (tensPure s (t + 1) (w + 1) (by omega) a (Sec.map (J.d t (t + 1)) b))) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (y : Sec (K.X w) U), Loc U fun V g => ∃ x, φ V w x = Sec.res g y) ∧
    (∀ (U : Scheme.{0}) (w : ℤ) (x : Tens I J U w), φ U w x = 0 → Loc U fun _ g => Tens.res g w x = 0)

theorem etale_tensor_complex_exists_of_sheaf_tensor_complex (hS : EtaleSheafTensorComplexExists) : EtaleComplexTensorPairingExists := by
  intro R _ I J
  obtain ⟨K, φ, hnat, hd, hsurj, hinj⟩ := hS R I J
  let μ : Pair I J K :=
    { mul := fun U s t w h => (TensorProduct.mk (ULift.{1} R) _ _).compr₂
          ((φ U w).comp (DirectSum.lof (ULift.{1} R) {p : ℤ × ℤ // p.1 + p.2 = w}
            (fun p => Sec (I.X p.1.1) U ⊗[ULift.{1} R] Sec (J.X p.1.2) U) ⟨(s, t), h⟩))
      nat := by
        intro V U g s t w h a b
        have := hnat g w (tensPure s t w h a b)
        simpa [tensPure, Tens.res, DirectSum.lmap_lof] using this
      leibniz := by
        intro U s t w h a b
        simpa [tensPure] using hd U s t w h a b }
  have hlift : ∀ U w, μ.lift U w = φ U w := by
    intro U w
    apply DirectSum.linearMap_ext
    intro p
    apply TensorProduct.ext'
    intro a b
    simp [Pair.lift, μ]
  refine ⟨K, μ, ?_, ?_⟩
  · intro U w y
    simpa [hlift] using hsurj U w y
  · intro U w x hx
    exact hinj U w x (by simpa [hlift] using hx)

end LateralTheory.EtaleFoundations
end
end

