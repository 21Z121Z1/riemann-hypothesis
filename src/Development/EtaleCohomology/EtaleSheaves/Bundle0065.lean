import Development.EtaleCohomology.EtaleSheaves.Bundle0059
import Development.EtaleCohomology.EtaleSheaves.Bundle0056
import Development.EtaleCohomology.EtaleSheaves.Bundle0058

-- bundled from Development.EtaleCohomology.EtaleSheaves.H1FiniteCoefficients
section
noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing

namespace LateralTheory.E.NoetherianChartOverlapFiniteComplement

variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

theorem exists_pow_mul_mem (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ n : ℕ, u⁻¹ ^ n * x ∈ S := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨0, by simpa using hx⟩
    · rw [Set.mem_singleton_iff] at hx; subst hx
      exact ⟨1, by rw [pow_one, inv_mul_cancel₀ hu]; exact S.one_mem⟩
  | algebraMap r => exact ⟨0, by simpa using S.algebraMap_mem r⟩
  | add x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x + y) = u⁻¹ ^ m * (u⁻¹ ^ n * x) + u⁻¹ ^ n * (u⁻¹ ^ m * y) := by ring
    rw [this]
    exact S.add_mem (S.mul_mem (S.pow_mem hv _) hn) (S.mul_mem (S.pow_mem hv _) hm)
  | mul x y _ _ ihx ihy =>
    obtain ⟨n, hn⟩ := ihx
    obtain ⟨m, hm⟩ := ihy
    refine ⟨n + m, ?_⟩
    have : u⁻¹ ^ (n + m) * (x * y) = (u⁻¹ ^ n * x) * (u⁻¹ ^ m * y) := by ring
    rw [this]; exact S.mul_mem hn hm

theorem pow_inv_mul_pow (t : K) (ht : t ≠ 0) (n j : ℕ) :
    (n ≤ j ∧ t⁻¹ ^ n * t ^ j = t ^ (j - n)) ∨ (j < n ∧ t⁻¹ ^ n * t ^ j = t⁻¹ ^ (n - j)) := by
  rcases le_or_gt n j with h | h
  · left
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ ht, one_pow, one_mul]
  · right
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le h.le
    refine ⟨h, ?_⟩
    rw [Nat.add_sub_cancel_left, pow_add, mul_comm (t⁻¹ ^ j), mul_assoc, ← mul_pow, inv_mul_cancel₀ ht,
      one_pow, mul_one]

theorem noetherian_local_chart_overlap_finite_complement : LateralTheory.E.LZIdemSumNoetherian.NoetherianLocalChartOverlapFiniteComplement := by
  intro A _ _ _ K _ _ B C t hc hB _
  obtain ⟨S, hS⟩ := hB
  set R := Algebra.adjoin A ({t} : Set K)
  have hfg : (Algebra.adjoin R (S : Set K)).toSubmodule.FG :=
    fg_adjoin_of_finite S.finite_toSet (fun x hx => hc.intB x (hS ▸ Algebra.subset_adjoin hx))
  obtain ⟨G, hG⟩ := hfg
  have hRB : ∀ r : R, (r : K) ∈ B := by
    intro r
    have : R ≤ B := Algebra.adjoin_le (by simpa using hc.tB)
    exact this r.2
  have hAB : ∀ y ∈ Algebra.adjoin R (S : Set K), y ∈ B := by
    intro y hy
    induction hy using Algebra.adjoin_induction with
    | mem x hx => exact hS ▸ Algebra.subset_adjoin hx
    | algebraMap r => exact hRB r
    | add x y _ _ hx hy => exact B.add_mem hx hy
    | mul x y _ _ hx hy => exact B.mul_mem hx hy
  have hGB : ∀ g ∈ G, g ∈ B := by
    intro g hg
    have : g ∈ (Algebra.adjoin R (S : Set K)).toSubmodule := hG ▸ Submodule.subset_span hg
    exact hAB g this
  have hBR : ∀ x ∈ B, x ∈ Submodule.span R (G : Set K) := by
    intro x hx
    rw [hG]
    rw [← hS] at hx
    show x ∈ Algebra.adjoin R (S : Set K)
    induction hx using Algebra.adjoin_induction with
    | mem y hy => exact Algebra.subset_adjoin hy
    | algebraMap a => exact ((Algebra.adjoin R (S : Set K)).restrictScalars A).algebraMap_mem a
    | add x y _ _ hx hy => exact Subalgebra.add_mem _ hx hy
    | mul x y _ _ hx hy => exact Subalgebra.mul_mem _ hx hy
  have hLex : ∀ g ∈ G, ∃ n : ℕ, t⁻¹ ^ n * g ∈ C := by
    intro g hg
    have : g ∈ Algebra.adjoin A ((C : Set K) ∪ {t}) := by
      rw [← hc.glue]; exact Algebra.subset_adjoin (Or.inl (hGB g hg))
    exact exists_pow_mul_mem C t hc.ne hc.tC this
  classical
  let Lf : K → ℕ := fun g => if h : ∃ n : ℕ, t⁻¹ ^ n * g ∈ C then Classical.choose h else 0
  let L := G.sup Lf
  have hL : ∀ g ∈ G, t⁻¹ ^ L * g ∈ C := by
    intro g hg
    have h := hLex g hg
    have hle : Lf g ≤ L := Finset.le_sup hg
    have hspec : t⁻¹ ^ Lf g * g ∈ C := by
      simp only [Lf, dif_pos h]; exact Classical.choose_spec h
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le hle
    rw [hk, pow_add, mul_comm (t⁻¹ ^ Lf g), mul_assoc]
    exact C.mul_mem (C.pow_mem hc.tC _) hspec
  let N : Submodule A K := Submodule.span A ↑((G ×ˢ Finset.range L).image (fun p => t⁻¹ ^ p.2 * p.1))
  refine ⟨N, ⟨_, rfl⟩, ?_⟩
  set T := Subalgebra.toSubmodule B ⊔ Subalgebra.toSubmodule C ⊔ N with hT
  have hCT : ∀ x ∈ C, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_right hx)
  have hBT : ∀ x ∈ B, x ∈ T := fun x hx => Submodule.mem_sup_left (Submodule.mem_sup_left hx)
  have core : ∀ g ∈ G, ∀ m : ℕ, t⁻¹ ^ m * g ∈ T := by
    intro g hg m
    rcases lt_or_ge m L with h | h
    · refine Submodule.mem_sup_right (Submodule.subset_span ?_)
      exact Finset.mem_coe.mpr (Finset.mem_image.mpr ⟨(g, m), Finset.mem_product.mpr ⟨hg, Finset.mem_range.mpr h⟩, rfl⟩)
    · obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le h
      rw [hk, pow_add, mul_comm (t⁻¹ ^ L), mul_assoc]
      exact hCT _ (C.mul_mem (C.pow_mem hc.tC _) (hL g hg))
  have core2 : ∀ g ∈ G, ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * g ∈ T := by
    intro g hg n j
    rcases pow_inv_mul_pow t hc.ne n j with ⟨_, h⟩ | ⟨_, h⟩
    · rw [h]; exact hBT _ (B.mul_mem (B.pow_mem hc.tB _) (hGB g hg))
    · rw [h]; exact core g hg _
  have hspan : ∀ x ∈ Submodule.span R (G : Set K), ∀ n j : ℕ, t⁻¹ ^ n * t ^ j * x ∈ T := by
    intro x hx
    induction hx using Submodule.span_induction with
    | mem g hg => exact core2 g hg
    | zero => intro n j; simp
    | add x y _ _ hx hy => intro n j; rw [mul_add]; exact T.add_mem (hx n j) (hy n j)
    | smul r x _ hx =>
      intro n j
      have hr : (r : K) ∈ (Polynomial.aeval (R := A) t).range := by
        rw [← Algebra.adjoin_singleton_eq_range_aeval A t]; exact r.2
      obtain ⟨p, hp⟩ := hr
      have hp' : Polynomial.aeval t p = (r : K) := hp
      have this : r • x = (r : K) * x := rfl
      rw [this, ← hp']
      clear hp hp' this
      induction p using Polynomial.induction_on' with
      | add p q hp' hq' =>
        rw [map_add, add_mul, mul_add]
        exact T.add_mem hp' hq'
      | monomial i a =>
        rw [Polynomial.aeval_monomial]
        have : t⁻¹ ^ n * t ^ j * (algebraMap A K a * t ^ i * x) = a • (t⁻¹ ^ n * t ^ (j + i) * x) := by
          rw [Algebra.smul_def, pow_add]; ring
        rw [this]; exact T.smul_mem a (hx n (j + i))
  intro x hx
  have hx' : x ∈ Algebra.adjoin A ((B : Set K) ∪ {t⁻¹}) := hx
  obtain ⟨n, hn⟩ := exists_pow_mul_mem B t⁻¹ (inv_ne_zero hc.ne) (by rw [inv_inv]; exact hc.tB) hx'
  rw [inv_inv] at hn
  have := hspan _ (hBR _ hn) n 0
  have e : t⁻¹ ^ n * t ^ 0 * (t ^ n * x) = x := by
    rw [pow_zero, mul_one, ← mul_assoc, ← mul_pow, inv_mul_cancel₀ hc.ne, one_pow, one_mul]
  rwa [e] at this

end LateralTheory.E.NoetherianChartOverlapFiniteComplement
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.ImageInPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace

namespace LateralTheory.E.ImageInPf

theorem vanishing_le_ker {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Scheme.IdealSheafData.vanishingIdeal (Closeds.closure (Set.range γ)) ≤ γ.ker := by
  rw [Scheme.Hom.ker, Scheme.IdealSheafData.le_ofIdeals_iff]
  intro U s hs
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal] at hs
  show s ∈ RingHom.ker (γ.app U).hom
  rw [RingHom.mem_ker]
  apply eq_zero_of_basicOpen_eq_bot
  rw [← Scheme.preimage_basicOpen, eq_bot_iff]
  intro x hx
  exfalso
  have hx' : γ x ∈ Y.basicOpen s := hx
  have hU : γ x ∈ U.1 := Y.basicOpen_le s hx'
  obtain ⟨y, hy⟩ : γ x ∈ Set.range U.2.fromSpec := by rw [U.2.range_fromSpec]; exact hU
  have h1 := hs y (by
    show U.2.fromSpec y ∈ closure (Set.range γ)
    rw [hy]; exact subset_closure ⟨x, rfl⟩)
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    show U.2.fromSpec y ∈ Y.basicOpen s
    rwa [hy]
  rw [U.2.fromSpec_preimage_basicOpen] at h2
  exact h2 h1

theorem ker_apply_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (U : Y.affineOpens) :
    γ.ker.ideal U = RingHom.ker (γ.app U).hom := by
  refine le_antisymm (γ.ideal_ker_le U) fun s hs => vanishing_le_ker γ U ?_
  simp only [Scheme.IdealSheafData.vanishingIdeal_ideal, PrimeSpectrum.mem_vanishingIdeal]
  intro y hy
  by_contra h
  have h2 : y ∈ U.2.fromSpec ⁻¹ᵁ Y.basicOpen s := by
    rw [U.2.fromSpec_preimage_basicOpen]; exact h
  have hy' : U.2.fromSpec y ∈ closure (Set.range γ) := hy
  obtain ⟨_, hz, x, rfl⟩ := mem_closure_iff.mp hy' _ (Y.basicOpen s).2 h2
  have h3 : x ∈ γ ⁻¹ᵁ Y.basicOpen s := hz
  rw [Scheme.preimage_basicOpen, RingHom.mem_ker.mp hs, Scheme.basicOpen_zero] at h3
  exact h3

theorem ker_restrict_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (U : O.toScheme.affineOpens) :
    (γ ∣_ O).ker.ideal U = γ.ker.ideal ⟨O.ι ''ᵁ U, U.2.image_of_isOpenImmersion _⟩ := by
  rw [ker_apply_red, ker_apply_red]
  ext x
  simpa [Scheme.Hom.appLE] using! map_eq_zero_iff _
    (ConcreteCategory.bijective_of_isIso (V.presheaf.map (eqToHom (image_morphismRestrict_preimage γ O U)).op)).1

theorem image_in_red {V Y Z : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) (O : Y.Opens) (t : Z ⟶ O.toScheme)
    (a : (γ ⁻¹ᵁ O).toScheme ⟶ Z) [IsClosedImmersion t] (h : a ≫ t = γ ∣_ O) :
    ∃ b : (γ.imageι ⁻¹ᵁ O).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ O := by
  have H : t.ker ≤ (γ.imageι ∣_ O).ker := by
    refine (a.le_ker_comp t).trans ?_
    rw [h]
    intro U
    rw [ker_restrict_red, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_rfl
  exact ⟨_, IsClosedImmersion.lift_fac t _ H⟩

theorem image_in_qc {V Y Z : Scheme.{0}} (γ : V ⟶ Y) [QuasiCompact γ] (O : Y.Opens) (t : Z ⟶ O.toScheme)
    (a : (γ ⁻¹ᵁ O).toScheme ⟶ Z) [IsClosedImmersion t] (h : a ≫ t = γ ∣_ O) :
    ∃ b : (γ.imageι ⁻¹ᵁ O).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ O := by
  have H : t.ker ≤ (γ.imageι ∣_ O).ker := by
    refine (a.le_ker_comp t).trans ?_
    rw [h]
    intro U
    rw [Scheme.ker_morphismRestrict_ideal, Scheme.ker_morphismRestrict_ideal, Scheme.Hom.imageι,
      Scheme.IdealSheafData.ker_subschemeι]
    exact le_rfl
  exact ⟨_, IsClosedImmersion.lift_fac t _ H⟩

theorem range_imageι_red {V Y : Scheme.{0}} [IsReduced V] (γ : V ⟶ Y) :
    Set.range γ.imageι ⊆ closure (Set.range γ) := by
  rw [Scheme.Hom.imageι, Scheme.IdealSheafData.range_subschemeι]
  have := Scheme.IdealSheafData.support_antitone (vanishing_le_ker γ)
  intro y hy
  have h2 := this hy
  exact h2

def ImageInR : Prop := ∀ {S X₁ : Scheme.{0}} [IsReduced X₁] (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j,
      ∀ (Z : Scheme.{0}) (t : Z ⟶ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).toScheme) (a : (γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z),
        IsClosedImmersion t → a ≫ t = γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) →
        ∃ b : (γ.imageι ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z, b ≫ t = γ.imageι ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))

theorem ImageInR_of : ImageInR := by
  intro S X₁ _ p₁ _ n U Pj qj W e P q π _ _ _ _ _ V _ hV γ _ _ j Z t a ht hat
  exact image_in_red γ _ t a hat

theorem covered_red {S X₁ : Scheme.{0}} [IsReduced X₁] (p₁ : X₁ ⟶ S)
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j)
    (hcov : ∀ x : X₁, ∃ j, x ∈ U j) (hsep : ∀ j, IsSeparated (qj j))
    (hc : ∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) (hπ : ∀ j, π j ≫ qj j = q)
    (V : X₁.Opens) (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q)
    (hγ1 : γ ≫ pullback.fst p₁ q = V.ι)
    (hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) :
      Set.range (γ.imageι ≫ pullback.snd p₁ q) ⊆ ⋃ j, ((π j ⁻¹ᵁ W j : P.Opens) : Set P) := by
  rintro _ ⟨y, rfl⟩
  have hz : γ.imageι y ∈ closure (Set.range γ) := range_imageι_red γ ⟨y, rfl⟩
  obtain ⟨j, hj⟩ := hcov (pullback.fst p₁ q (γ.imageι y))
  refine Set.mem_iUnion.mpr ⟨j, ?_⟩
  set z := γ.imageι y
  let O : (pullback p₁ q).Opens := pullback.fst p₁ q ⁻¹ᵁ U j
  have hcomm : ((pullback.fst p₁ q ∣_ U j) ≫ e j ≫ (W j).ι) ≫ qj j = (O.ι ≫ pullback.snd p₁ q ≫ π j) ≫ qj j := by
    simp only [Category.assoc, hc j, hπ j, morphismRestrict_ι_assoc, pullback.condition]
    rfl
  let f : O.toScheme ⟶ pullback (qj j) (qj j) := pullback.lift _ _ hcomm
  have hD : IsClosed (Set.range (pullback.diagonal (qj j))) :=
    (pullback.diagonal (qj j)).isClosedEmbedding.isClosed_range
  have hrange : Set.range γ ⊆ Set.range O.ι := by
    rintro _ ⟨v, rfl⟩
    rw [Scheme.Opens.range_ι]
    show pullback.fst p₁ q (γ v) ∈ U j
    rw [← Scheme.Hom.comp_apply, hγ1]
    exact hV j v.2
  let γO : V.toScheme ⟶ O.toScheme := IsOpenImmersion.lift O.ι γ hrange
  have hγO : γO ≫ O.ι = γ := IsOpenImmersion.lift_fac _ _ _
  have hfac : γO ≫ f = (X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) ≫ pullback.diagonal (qj j) := by
    apply pullback.hom_ext
    · simp only [f, Category.assoc, pullback.lift_fst, pullback.diagonal_fst, Category.comp_id]
      have h1 : γO ≫ (pullback.fst p₁ q ∣_ U j) = X₁.homOfLE (hV j) := by
        rw [← cancel_mono (U j).ι, Category.assoc, morphismRestrict_ι, reassoc_of% hγO, hγ1,
          Scheme.homOfLE_ι]
      rw [reassoc_of% h1]
    · simp only [f, Category.assoc, pullback.lift_snd, pullback.diagonal_snd, Category.comp_id]
      rw [← hγ2 j, ← hγO, Category.assoc]
  obtain ⟨zO, hzO⟩ : z ∈ Set.range O.ι := by rw [Scheme.Opens.range_ι]; exact hj
  have hcl : zO ∈ closure (O.ι ⁻¹' Set.range γ) := by
    rw [← O.ι.isOpenEmbedding.isOpenMap.preimage_closure_eq_closure_preimage O.ι.continuous]
    show O.ι zO ∈ closure (Set.range γ)
    rw [hzO]; exact hz
  have hsub : O.ι ⁻¹' Set.range γ ⊆ f ⁻¹' Set.range (pullback.diagonal (qj j)) := by
    rintro w ⟨v, hv⟩
    have hw : w = γO v := O.ι.isOpenEmbedding.injective (by
      rw [← Scheme.Hom.comp_apply, hγO, hv])
    refine ⟨(X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) v, ?_⟩
    rw [hw, ← Scheme.Hom.comp_apply, ← hfac, Scheme.Hom.comp_apply]
  obtain ⟨p, hp⟩ := closure_minimal hsub (hD.preimage f.continuous) hcl
  have e1 : (f ≫ pullback.fst _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_fst]; rfl
  have e2 : (f ≫ pullback.snd _ _) zO = p := by
    rw [Scheme.Hom.comp_apply, ← hp, ← Scheme.Hom.comp_apply, pullback.diagonal_snd]; rfl
  simp only [f, pullback.lift_fst, pullback.lift_snd] at e1 e2
  show π j (pullback.snd p₁ q z) ∈ W j
  have : π j (pullback.snd p₁ q z) = p := by
    rw [← e2, ← hzO]; simp only [Scheme.Hom.comp_apply]
  rw [this, ← e1]
  simp only [Scheme.Hom.comp_apply]
  have hmem : ∀ a : (W j).toScheme, (W j).ι a ∈ W j := fun a => by
    exact (Scheme.Opens.range_ι (W j)).le ⟨a, rfl⟩
  exact hmem _

def GraphT : Prop := ∀ {S X₁ : Scheme.{0}} (p₁ : X₁ ⟶ S) [IsProper p₁]
  (n : ℕ) (U : Fin n → X₁.Opens) (Pj : Fin n → Scheme.{0}) (qj : ∀ j, Pj j ⟶ S) (W : ∀ j, (Pj j).Opens)
    (e : ∀ j, (U j).toScheme ⟶ (W j).toScheme) (P : Scheme.{0}) (q : P ⟶ S) (π : ∀ j, P ⟶ Pj j),
    (∀ x : X₁, ∃ j, x ∈ U j) → (∀ j, IsSeparated (qj j)) →
    (∀ j, IsClosedImmersion (e j)) → (∀ j, e j ≫ (W j).ι ≫ qj j = (U j).ι ≫ p₁) → (∀ j, π j ≫ qj j = q) →
    ∀ (V : X₁.Opens), IsAffineOpen V → ∀ (hV : ∀ j, V ≤ U j) (γ : V.toScheme ⟶ pullback p₁ q),
      γ ≫ pullback.fst p₁ q = V.ι → (∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) →
      ∀ j,
      ∃ (Z : Scheme.{0}) (t : Z ⟶ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).toScheme) (a : (γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).toScheme ⟶ Z),
        IsClosedImmersion t ∧ IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ∧
        a ≫ t = γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))

theorem GraphT_of : GraphT := by
  intro S X₁ p₁ _ n U Pj qj W e P q π _ _ he hc hπ V _ hV γ h1 h2 j
  have := he j
  let z1 := pullback.fst (π j ∣_ W j) (e j)
  let z2 := pullback.snd (π j ∣_ W j) (e j)
  have hz : z1 ≫ (π j ∣_ W j) = z2 ≫ e j := pullback.condition
  have hw : (z2 ≫ (U j).ι) ≫ p₁ = (z1 ≫ (π j ⁻¹ᵁ W j).ι) ≫ q := by
    rw [Category.assoc, ← hc j, ← reassoc_of% hz, morphismRestrict_ι_assoc, hπ j, Category.assoc]
  let t0 := pullback.lift _ _ hw
  have hP := isPullback_morphismRestrict (pullback.snd p₁ q) (π j ⁻¹ᵁ W j)
  have ht0 : z1 ≫ (π j ⁻¹ᵁ W j).ι = t0 ≫ pullback.snd p₁ q := (pullback.lift_snd _ _ _).symm
  have ht0' : t0 ≫ pullback.fst p₁ q = z2 ≫ (U j).ι := pullback.lift_fst _ _ _
  let t := hP.lift z1 t0 ht0
  have e1 : t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j) = z1 := hP.lift_fst _ _ _
  have e2 : t ≫ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)).ι = t0 := hP.lift_snd _ _ _
  have hcl : IsClosedImmersion (t ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) := by rw [e1]; infer_instance
  have ha : (γ ∣_ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j)) ≫ pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)) ≫ (π j ∣_ W j) =
      ((γ ⁻¹ᵁ (pullback.snd p₁ q ⁻¹ᵁ (π j ⁻¹ᵁ W j))).ι ≫ X₁.homOfLE (hV j)) ≫ e j := by
    rw [← cancel_mono (W j).ι]
    simp only [Category.assoc, morphismRestrict_ι, morphismRestrict_ι_assoc, h2 j]
  let a := pullback.lift _ _ ha
  have a1 : a ≫ z1 = _ := pullback.lift_fst _ _ _
  have a2 : a ≫ z2 = _ := pullback.lift_snd _ _ _
  refine ⟨_, t, a, IsClosedImmersion.of_comp t (pullback.snd p₁ q ∣_ (π j ⁻¹ᵁ W j)), hcl, ?_⟩
  apply hP.hom_ext
  · rw [Category.assoc, e1, a1]
  · rw [Category.assoc, e2, morphismRestrict_ι]
    apply pullback.hom_ext
    · rw [Category.assoc, ht0', reassoc_of% a2, Scheme.homOfLE_ι, Category.assoc, h1]
    · rw [Category.assoc, ← ht0, reassoc_of% a1, morphismRestrict_ι, morphismRestrict_ι_assoc, Category.assoc]

theorem Core_of : LateralTheory.E.ChowGraphCut.Core := by
  intro S X₁ p₁ _ hX n U Pj qj W e P q π hUn hUc hsep he hc hπ hUP
  obtain ⟨x₀⟩ : Nonempty X₁ := inferInstance
  obtain ⟨j₀, -⟩ := hUc x₀
  let V₀ : X₁.Opens := Finset.univ.inf U
  have hV₀ : ∀ j, V₀ ≤ U j := fun j => Finset.inf_le (Finset.mem_univ j)
  obtain ⟨x, hx⟩ := LateralTheory.E.CorePf.inf_nonempty U hUn _ ⟨j₀, Finset.mem_univ _⟩
  obtain ⟨V', hVa, hxV, hVle⟩ :=
    TopologicalSpace.Opens.isBasis_iff_nbhd.mp X₁.isBasis_affineOpens (U := V₀) hx
  obtain ⟨V, rfl⟩ : ∃ V : X₁.Opens, V = V' := ⟨V', rfl⟩
  replace hVa : IsAffineOpen V := hVa
  have hV : ∀ j, (V : X₁.Opens) ≤ U j := fun j => hVle.trans (hV₀ j)
  obtain ⟨g, ⟨hg1, hg2⟩, -⟩ := hUP ((V : X₁.Opens).ι ≫ p₁) (fun j => X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι) (by
    intro j
    simp only [Category.assoc, hc j, Scheme.homOfLE_ι_assoc])
  let γ : (V : X₁.Opens).toScheme ⟶ pullback p₁ q := pullback.lift (V : X₁.Opens).ι g hg1.symm
  have hγ1 : γ ≫ pullback.fst p₁ q = (V : X₁.Opens).ι := pullback.lift_fst _ _ _
  have hγ2 : ∀ j, γ ≫ pullback.snd p₁ q ≫ π j = X₁.homOfLE (hV j) ≫ e j ≫ (W j).ι := by
    intro j; rw [pullback.lift_snd_assoc, hg2 j]
  refine ⟨γ.image, γ.imageι, V, γ.toImage, inferInstance,
    LateralTheory.E.CorePf2.isClosedImmersion_of_cover _ (fun j => π j ⁻¹ᵁ W j) (LateralTheory.E.CorePf2.range_closed p₁ q γ)
      (covered_red p₁ n U Pj qj W e P q π hUc hsep hc hπ V hV γ hγ1 hγ2)
      (fun j => ?_), ⟨x, hxV⟩, ?_⟩
  · obtain ⟨Z, t, a, ht, hts, hat⟩ := GraphT_of p₁ n U Pj qj W e P q π hUc hsep he hc hπ V hVa hV γ hγ1 hγ2 j
    obtain ⟨b, hb⟩ := image_in_red γ _ t a hat
    rw [morphismRestrict_comp, ← hb, Category.assoc]
    have : IsClosedImmersion (b ≫ t) := by rw [hb]; infer_instance
    have : IsClosedImmersion b := IsClosedImmersion.of_comp_isClosedImmersion b t
    exact @IsClosedImmersion.comp _ _ _ b _ this hts
  · rw [Scheme.Hom.toImage_imageι_assoc, hγ1]

end LateralTheory.E.ImageInPf
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafClosedSHPosPf
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite Polynomial IsLocalRing GlobalTheory.EtC LateralTheory.E.E4

namespace LateralTheory.E.LeafClosedSHPosPf

theorem hens_of_surj {A B : Type} [CommRing A] [CommRing B] [HenselianLocalRing A] [Nontrivial B]
    (φ : A →+* B) (hφ : Function.Surjective φ) : HenselianLocalRing B := by
  have := IsLocalHom.of_surjective φ hφ
  have : IsLocalRing B := IsLocalRing.of_surjective φ hφ
  refine { is_henselian := ?_ }
  intro f hf a₀ h₁ h₂
  have hl : f ∈ Polynomial.lifts φ := (Polynomial.lifts_iff_coeff_lifts f).2 (fun n => hφ _)
  obtain ⟨g, hg, -, hgm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hl hf
  obtain ⟨b₀, rfl⟩ := hφ a₀
  have hev : ∀ (p : A[X]) (x : A), (p.map φ).eval (φ x) = φ (p.eval x) := fun p x => by
    rw [Polynomial.eval_map, eval₂_at_apply]
  subst hg
  have h1 : g.eval b₀ ∈ maximalIdeal A := by
    rw [hev] at h₁
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 h₁ (hu.map φ))
  have h2 : IsUnit (g.derivative.eval b₀) := by
    rw [derivative_map, hev] at h₂
    exact IsUnit.of_map φ _ h₂
  obtain ⟨a, ha, ham⟩ := HenselianLocalRing.is_henselian g hgm b₀ h1 h2
  refine ⟨φ a, ?_, ?_⟩
  · rw [IsRoot, hev, ha.eq_zero, map_zero]
  · rw [← map_sub]
    exact (mem_maximalIdeal _).2 (fun hu => (mem_maximalIdeal _).1 ham (IsUnit.of_map φ _ hu))

theorem sepClosed_of_surj {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A] [IsLocalRing B]
    (φ : A →+* B) [IsLocalHom φ] (hφ : Function.Surjective φ) [IsSepClosed (ResidueField A)] :
    IsSepClosed (ResidueField B) := by
  have hs : Function.Surjective (ResidueField.map φ) := by
    intro y
    obtain ⟨b, rfl⟩ := residue_surjective y
    obtain ⟨a, rfl⟩ := hφ b
    exact ⟨residue A a, ResidueField.map_residue φ a⟩
  let e : ResidueField A ≃+* ResidueField B :=
    RingEquiv.ofBijective (ResidueField.map φ) ⟨(ResidueField.map φ).injective, hs⟩
  refine ⟨fun p hp => ?_⟩
  have h1 : (p.map (e.symm : ResidueField B →+* ResidueField A)).Separable := hp.map
  have h2 := (IsSepClosed.splits_of_separable _ h1).map (e : ResidueField A →+* ResidueField B)
  rw [Polynomial.map_map] at h2
  convert h2
  ext x; simp

theorem sub_of_iso {X Y : Scheme.{0}} (e : X ≅ Y) (R : Type) [CommRing R] (F : Shv R) (n : ℤ)
    (h : Subsingleton (H R (sch.obj Y) F n)) : Subsingleton (H R (sch.obj X) F n) := by
  refine ⟨fun x y => ?_⟩
  have key : ∀ z : H R (sch.obj X) F n,
      z = pull R (sch.map e.hom) F n (pull R (sch.map e.inv) F n z) := by
    intro z
    rw [← pull_comp, ← CategoryTheory.Functor.map_comp, e.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  rw [key x, key y, Subsingleton.elim (pull R (sch.map e.inv) F n x) (pull R (sch.map e.inv) F n y)]

theorem sub_of_empty (hy : Hyps) (R : Type) [CommRing R] (F : Shv R) (W : Scheme.{0}) [IsEmpty W] (n : ℤ)
    (hn : 0 < n) : Subsingleton (H R (sch.obj W) F n) := by
  have a5 : A5 := hy.2.2.2.2.1
  suffices h : ∀ x : H R (sch.obj W) F n, x = 0 from ⟨fun a b => by rw [h a, h b]⟩
  intro x
  obtain ⟨Z, f, -, -, hf⟩ := a5 R W F n hn x
  have : IsEmpty Z := ⟨fun z => isEmptyElim (f.base z)⟩
  let g : W ⟶ Z := (isInitialOfIsEmpty (X := W)).to Z
  have hgf : g ≫ f = 𝟙 W := (isInitialOfIsEmpty (X := W)).hom_ext _ _
  have : pull R (sch.map (g ≫ f)) F n x = x := by rw [hgf, CategoryTheory.Functor.map_id, pull_id]
  rw [← this, CategoryTheory.Functor.map_comp, pull_comp, hf, map_zero]

theorem LeafClosedSHPos_of : LateralTheory.E.LeafVanBPf.LeafClosedSHPos := by
  intro hy q _ i A _ _ hA hq W' ι' _ n hn
  rcases isEmpty_or_nonempty W' with hW | ⟨⟨w⟩⟩
  · exact sub_of_empty hy _ _ W' n hn
  obtain ⟨hAff, hsurj⟩ := IsClosedImmersion.isAffine_surjective_of_isAffine ι'
  let B : Type := Γ(W', ⊤)
  let ψ : A →+* B := (ι'.appTop).hom.comp (Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom
  have hψ : Function.Surjective ψ := hsurj.comp
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of A)).inv).2
  have : Nontrivial B := by
    by_contra hB
    rw [not_nontrivial_iff_subsingleton] at hB
    let p := W'.isoSpec.hom.base w
    exact p.isPrime.ne_top (Subsingleton.elim _ _)
  obtain ⟨hH, hS⟩ := hA
  have := IsLocalHom.of_surjective ψ hψ
  have hHB : HenselianLocalRing B := hens_of_surj ψ hψ
  have hSB : SH B := ⟨hHB, sepClosed_of_surj ψ hψ⟩
  have h2 := LateralTheory.E.LeafVanBPf.heightFunctionalStatement_of_pairingProperties hy (ZMod q) B hSB (tw q i) n hn
  exact sub_of_iso W'.isoSpec (ZMod q) (tw q i) n h2

end LateralTheory.E.LeafClosedSHPosPf
end
end

