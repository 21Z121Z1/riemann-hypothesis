import Mathlib

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenConnectedComponentOfIsLocallyNoetherian
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

set_option autoImplicit false

namespace GlobalTheory.ConnOpen

theorem isOpen_connectedComponent_noetherian {Y : Type*} [TopologicalSpace Y] [NoetherianSpace Y] (y : Y) :
    IsOpen (connectedComponent y) := by
  set C := connectedComponent y
  have key : ∀ t, t ∉ C → irreducibleComponent t ⊆ Cᶜ := by
    intro t ht s hs hsC
    have h1 : irreducibleComponent t ⊆ connectedComponent s :=
      _root_.IsPreconnected.subset_connectedComponent
        (isIrreducible_irreducibleComponent (x := t)).isConnected.isPreconnected hs
    rw [← connectedComponent_eq hsC] at h1
    exact ht (h1 mem_irreducibleComponent)
  have hC : Cᶜ = ⋃ Z ∈ {Z ∈ irreducibleComponents Y | Z ⊆ Cᶜ}, Z := by
    ext t
    refine ⟨fun ht => Set.mem_biUnion ⟨irreducibleComponent_mem_irreducibleComponents t, key t ht⟩
      mem_irreducibleComponent, fun ht => ?_⟩
    obtain ⟨Z, ⟨-, hZ⟩, htZ⟩ := Set.mem_iUnion₂.1 ht
    exact hZ htZ
  have hcl : IsClosed Cᶜ := by
    rw [hC]
    exact (NoetherianSpace.finite_irreducibleComponents.subset fun _ h => h.1).isClosed_biUnion
      fun Z h => isClosed_of_mem_irreducibleComponents Z h.1
  exact isClosed_compl_iff.1 hcl

end GlobalTheory.ConnOpen

theorem GlobalTheory.isOpen_connectedComponent_of_isLocallyNoetherian :
    ∀ (X : Scheme.{0}), IsLocallyNoetherian X → ∀ x : X, IsOpen (connectedComponent x) := by
  intro X hX x
  rw [isOpen_iff_forall_mem_open]
  intro y hy
  obtain ⟨U, hU, hyU, -⟩ := exists_isAffineOpen_mem_and_subset (X := X) (U := ⊤) (x := y) trivial
  haveI : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  haveI : NoetherianSpace (U : Set X) := noetherianSpace_of_isAffineOpen U hU
  let y' : (U : Set X) := ⟨y, hyU⟩
  refine ⟨Subtype.val '' connectedComponent y', ?_,
    U.isOpen.isOpenEmbedding_subtypeVal.isOpenMap _ (GlobalTheory.ConnOpen.isOpen_connectedComponent_noetherian y'),
    ⟨y', mem_connectedComponent, rfl⟩⟩
  have hc : _root_.IsPreconnected (Subtype.val '' connectedComponent y' : Set X) :=
    isPreconnected_connectedComponent.image _ continuous_subtype_val.continuousOn
  have := hc.subset_connectedComponent ⟨y', mem_connectedComponent, rfl⟩
  rwa [← connectedComponent_eq hy] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfConstructible
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory

def ultrafilterPrime {A : Type} [CommRing A] (U : Ultrafilter (PrimeSpectrum A)) :
    PrimeSpectrum A where
  asIdeal :=
    { carrier := {c | ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal}
      add_mem' := fun {a b} ha hb => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        have hb' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), b ∈ t.asIdeal := hb
        exact (ha'.and hb').mono fun t ht => t.asIdeal.add_mem ht.1 ht.2
      zero_mem' := Filter.Eventually.of_forall fun t => t.asIdeal.zero_mem
      smul_mem' := fun r a ha => by
        have ha' : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∈ t.asIdeal := ha
        exact ha'.mono fun t ht => t.asIdeal.mul_mem_left r ht }
  isPrime :=
    { ne_top' := fun h => by
        have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), (1 : A) ∈ t.asIdeal :=
          (Ideal.eq_top_iff_one _).1 h
        obtain ⟨t, ht⟩ := h1.exists
        exact t.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 ht)
      mem_or_mem' := fun {a b} hab => by
        have h : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a * b ∈ t.asIdeal := hab
        exact Ultrafilter.eventually_or.1 (h.mono fun t ht => t.isPrime.mem_or_mem ht) }

theorem isOpen_of_stableUnderGeneralization_of_constructible_pieces :
    ∀ (A : Type) [CommRing A] (Z : Set (PrimeSpectrum A)), StableUnderGeneralization Z → (∀ p ∈ Z, ∃ (a : A) (I : Finset A), a ∉ p.asIdeal ∧ (∀ c ∈ I, c ∈ p.asIdeal) ∧ ∀ t : PrimeSpectrum A, a ∉ t.asIdeal → (∀ c ∈ I, c ∈ t.asIdeal) → t ∈ Z) → IsOpen Z := by
  intro A _ Z hZ hpc
  rw [isOpen_iff_mem_nhds]
  intro p hp
  by_contra hn
  have hne : (nhds p ⊓ Filter.principal Zᶜ).NeBot := by
    rw [Filter.neBot_iff, Ne, Filter.inf_principal_eq_bot, compl_compl]
    exact hn
  obtain ⟨U, hU⟩ := Ultrafilter.exists_le (nhds p ⊓ Filter.principal Zᶜ)
  have hU1 : (U : Filter (PrimeSpectrum A)) ≤ nhds p := hU.trans inf_le_left
  have hU2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), t ∉ Z :=
    Filter.le_principal_iff.1 (hU.trans inf_le_right)
  have hle : ultrafilterPrime U ≤ p := by
    intro c hc
    by_contra hcp
    have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∈ t.asIdeal := hc
    have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), c ∉ t.asIdeal :=
      hU1 ((PrimeSpectrum.basicOpen c).isOpen.mem_nhds hcp)
    obtain ⟨t, ht1, ht2⟩ := (h1.and h2).exists
    exact ht2 ht1
  have hq : ultrafilterPrime U ∈ Z :=
    hZ ((PrimeSpectrum.le_iff_specializes _ _).1 hle |> fun h => by simpa using h) hp
  obtain ⟨a, I, ha, hI, hsub⟩ := hpc _ hq
  have h1 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), a ∉ t.asIdeal :=
    Ultrafilter.eventually_not.2 ha
  have h2 : ∀ᶠ t in (U : Filter (PrimeSpectrum A)), ∀ c ∈ I, c ∈ t.asIdeal :=
    (Filter.eventually_all_finset I).2 fun c hc => hI c hc
  obtain ⟨t, ⟨ht1, ht2⟩, ht3⟩ := ((h1.and h2).and hU2).exists
  exact ht3 (hsub t ht1 ht2)

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenOfStableUnderGeneralizationOfLocallyOpen
section
open IsLocalRing TensorProduct

namespace GlobalTheory

theorem isOpen_of_stableUnderGeneralization_of_locally_open_in_closure :
    ∀ (B : Type) [CommRing B] [IsNoetherianRing B] (U : Set (PrimeSpectrum B)),
      (∀ p q : PrimeSpectrum B, p ≤ q → q ∈ U → p ∈ U) →
      (∀ p ∈ U, ∃ g, g ∉ p.asIdeal ∧ ∀ q : PrimeSpectrum B, p ≤ q → g ∉ q.asIdeal → q ∈ U) →
      IsOpen U := by
  intro B _ _ U hgen hloc
  classical
  set I := PrimeSpectrum.vanishingIdeal (Uᶜ) with hI
  have hIle : ∀ q : PrimeSpectrum B, q ∈ Uᶜ → I ≤ q.asIdeal := by
    intro q hq f hf
    exact (PrimeSpectrum.mem_vanishingIdeal _ f).1 hf q hq
  have key : ∀ x : PrimeSpectrum B, x.asIdeal ∈ I.minimalPrimes → x ∉ U := by
    intro x hx hxU
    obtain ⟨g, hg, hgU⟩ := hloc x hxU
    have hfin := Ideal.finite_minimalPrimes_of_isNoetherianRing B I
    set S := hfin.toFinset.erase x.asIdeal with hS
    have hJ : ¬ S.inf id ≤ x.asIdeal := by
      intro h
      obtain ⟨P, hPS, hPx⟩ := (Ideal.IsPrime.inf_le' x.isPrime).1 h
      have hPm : P ∈ I.minimalPrimes := (Set.Finite.mem_toFinset hfin).1 (Finset.mem_of_mem_erase hPS)
      have hne : P ≠ x.asIdeal := Finset.ne_of_mem_erase hPS
      exact hne (le_antisymm hPx (hx.2 hPm.1 hPx))
    obtain ⟨c, hcJ, hcx⟩ := Set.not_subset.1 hJ
    have hgc : g * c ∈ I := by
      rw [hI, PrimeSpectrum.mem_vanishingIdeal]
      intro q hq
      obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le (hIle q hq)
      by_cases hPx : P = x.asIdeal
      · by_cases hgq : g ∈ q.asIdeal
        · exact q.asIdeal.mul_mem_right c hgq
        · exact absurd (hgU q (show x.asIdeal ≤ q.asIdeal by rw [← hPx]; exact hPq) hgq) hq
      · have hPS : P ∈ S := Finset.mem_erase.2 ⟨hPx, (Set.Finite.mem_toFinset hfin).2 hPm⟩
        have : S.inf id ≤ P := Finset.inf_le (f := id) hPS
        exact q.asIdeal.mul_mem_left g (hPq (this hcJ))
    rcases x.isPrime.mem_or_mem (hx.1.2 hgc) with h | h
    · exact hg h
    · exact hcx h
  have hcl : IsClosed (Uᶜ) := by
    rw [← closure_subset_iff_isClosed, ← PrimeSpectrum.zeroLocus_vanishingIdeal_eq_closure]
    intro q hq
    have hIq : I ≤ q.asIdeal := (PrimeSpectrum.mem_zeroLocus _ _).1 hq
    obtain ⟨P, hPm, hPq⟩ := Ideal.exists_minimalPrimes_le hIq
    intro hqU
    exact key ⟨P, hPm.1.1⟩ hPm (hgen _ _ hPq hqU)
  exact isClosed_compl_iff.1 hcl

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsOpenSndImageMulMemOpenGroupScheme
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory.IdCompOpen

theorem isOpen_snd_image : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G], Smooth G.hom → ∀ U : G.left.Opens,
    IsOpen {y : G.left | ∃ w : (G ⊗ G).left, (fst G G).left w ∈ U ∧ (μ[G]).left w ∈ U ∧ (snd G G).left w = y} := by
  intro S G _ hG U
  have hs : Smooth (pullback.snd G.hom G.hom) := inferInstance
  have ho : UniversallyOpen (pullback.snd G.hom G.hom) := UniversallyOpen.of_flat _
  have hmap : IsOpenMap (snd G G).left := (pullback.snd G.hom G.hom).isOpenMap
  have hW : IsOpen ((fst G G).left ⁻¹' (U : Set G.left) ∩ (μ[G]).left ⁻¹' (U : Set G.left)) :=
    ((U.isOpen.preimage (fst G G).left.continuous)).inter (U.isOpen.preimage (μ[G]).left.continuous)
  convert hmap _ hW using 1
  ext y
  simp only [Set.mem_setOf_eq, Set.mem_image, Set.mem_inter_iff, Set.mem_preimage, SetLike.mem_coe]
  constructor
  · rintro ⟨w, h1, h2, h3⟩; exact ⟨w, ⟨h1, h2⟩, h3⟩
  · rintro ⟨w, ⟨h1, h2⟩, h3⟩; exact ⟨w, h1, h2, h3⟩

end GlobalTheory.IdCompOpen
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPrimeSpanOfSqEqNegPrime
section
open NumberField

namespace GlobalTheory.CMModel

theorem isPrime_span_of_sq_eq_neg_prime :
    ∀ (p : ℕ) (K : Type) [Field K] [NumberField K] (y : 𝓞 K), p.Prime → Module.finrank ℚ K = 2 →
      y ^ 2 = -(p : 𝓞 K) → (Ideal.span {y}).IsPrime := by
  intro p K _ _ y hp hK hy
  have hr : Module.finrank ℤ (𝓞 K) = 2 := by rw [RingOfIntegers.rank, hK]
  have h1 : Ideal.absNorm (Ideal.span {y}) ^ 2 = p ^ 2 := by
    rw [← map_pow, Ideal.span_singleton_pow, hy, Ideal.span_singleton_neg,
      Ideal.absNorm_span_singleton]
    have : (p : 𝓞 K) = algebraMap ℤ (𝓞 K) (p : ℤ) := by simp
    rw [this, Algebra.norm_algebraMap, hr]
    simp [Int.natAbs_pow]
  have h2 : Ideal.absNorm (Ideal.span {y}) = p :=
    Nat.pow_left_injective (by norm_num : (2 : ℕ) ≠ 0) h1
  apply Ideal.isPrime_of_irreducible_absNorm
  rw [h2]
  exact (Nat.irreducible_iff_nat_prime p).2 hp

end GlobalTheory.CMModel
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsProperEighthFibrePowerOver
section
open AlgebraicGeometry CategoryTheory Limits

namespace GlobalTheory.FibrePowerProper

theorem isProper_hom_of_iso {T : Scheme.{0}} {X Y : Over T} (e : X ≅ Y) (h : IsProper Y.hom) :
    IsProper X.hom := by
  have hw : X.hom = e.hom.left ≫ Y.hom := (Over.w e.hom).symm
  haveI : IsIso e.hom.left := (Over.forget T).map_isIso e.hom
  rw [hw]
  infer_instance

theorem isProper_prod_hom {T : Scheme.{0}} (X Y : Over T) (hX : IsProper X.hom)
    (hY : IsProper Y.hom) : IsProper (X ⨯ Y).hom := by
  have h1 : (X ⨯ Y).hom = (Over.prodLeftIsoPullback X Y).hom ≫ pullback.fst X.hom Y.hom ≫ X.hom := by
    rw [← Category.assoc, Over.prodLeftIsoPullback_hom_fst]
    exact (Over.w (prod.fst : X ⨯ Y ⟶ X)).symm
  have hfst : IsProper (pullback.fst X.hom Y.hom) := by haveI := hY; infer_instance
  rw [h1]
  infer_instance

theorem isProper_fan_pt {T : Scheme.{0}} : ∀ (n : ℕ) (f : Fin n → Over T),
    (∀ i, IsProper (f i).hom) → ∀ (c : Fan f), IsLimit c → IsProper c.pt.hom
  | 0, f, _, c, hc => by
      have h0 : IsLimit (Fan.mk (Over.mk (𝟙 T)) (fun i => i.elim0 : ∀ i, Over.mk (𝟙 T) ⟶ f i)) :=
        Fan.IsLimit.mk _ (fun _ => Over.mkIdTerminal.from _) (fun _ k => k.elim0)
          (fun _ _ _ => Over.mkIdTerminal.hom_ext _ _)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso h0) (by dsimp; infer_instance)
  | n + 1, f, hf, c, hc => by
      let c₁ : Fan (fun i : Fin n => f i.succ) := limit.cone (Discrete.functor fun i : Fin n => f i.succ)
      have h1 : IsProper c₁.pt.hom :=
        isProper_fan_pt n (fun i => f i.succ) (fun i => hf _) c₁ (limit.isLimit _)
      have hl := extendFanIsLimit f (limit.isLimit (Discrete.functor fun i : Fin n => f i.succ))
        (prodIsProd (f 0) c₁.pt)
      exact isProper_hom_of_iso (hc.conePointUniqueUpToIso hl) (isProper_prod_hom _ _ (hf 0) h1)

theorem isProper_eighth_fibre_power : ∀ {T : Scheme.{0}} {B C : Over T} (pr : Fin 8 → (B ⟶ C)),
    (∀ (T' : Over T) (y : Fin 8 → (T' ⟶ C)), ∃! x : T' ⟶ B, ∀ a, x ≫ pr a = y a) →
    IsProper C.hom → IsProper B.hom := by
  intro T B C pr hu hC
  have hl : IsLimit (Fan.mk B pr) :=
    Fan.IsLimit.mk _ (fun s => (hu s.pt s.proj).choose)
      (fun s a => (hu s.pt s.proj).choose_spec.1 a)
      (fun s m hm => (hu s.pt s.proj).choose_spec.2 m hm)
  exact isProper_fan_pt 8 (fun _ => C) (fun _ => hC) _ hl

end GlobalTheory.FibrePowerProper
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsPullbackAppOfIsBasisOpens
section
open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.PinchBasis

theorem isPullback_iff_elem {A B C D : CommRingCat.{0}} (f : A ⟶ B) (g : A ⟶ C) (h : B ⟶ D) (i : C ⟶ D)
    (w : f ≫ h = g ≫ i) :
    IsPullback f g h i ↔ (∀ x y, f.hom x = f.hom y → g.hom x = g.hom y → x = y) ∧
      ∀ b c, h.hom b = i.hom c → ∃ a, f.hom a = b ∧ g.hom a = c := by
  constructor
  · intro H
    have H' := (Types.isPullback_iff _ _ _ _).1 (H.map (forget CommRingCat))
    exact ⟨fun x y hx hy ↦ H'.2.1 x y ⟨hx, hy⟩, fun b c hbc ↦ H'.2.2 b c hbc⟩
  · rintro ⟨h₁, h₂⟩
    refine IsPullback.of_map (forget CommRingCat) w ((Types.isPullback_iff _ _ _ _).2 ⟨?_, ?_, ?_⟩)
    · ext x
      simpa using congrArg (fun φ : A ⟶ D ↦ φ.hom x) w
    · exact fun x y hxy ↦ h₁ x y hxy.1 hxy.2
    · exact fun b c hbc ↦ h₂ b c hbc

lemma app_res {X Y : Scheme.{0}} (f : X ⟶ Y) {W V : Y.Opens} (i : W ⟶ V) (s : Γ(Y, V)) :
    (f.app W).hom ((Y.presheaf.map i.op).hom s) =
      (X.presheaf.map ((TopologicalSpace.Opens.map f.base).map i).op).hom ((f.app V).hom s) :=
  congrArg (fun φ => φ.hom s) (f.naturality i.op)

lemma appLE_res {X Y : Scheme.{0}} (g : X ⟶ Y) {U U' : Y.Opens} {V V' : X.Opens} (hU : U' ≤ U)
    (hV : V' ≤ V) (e : V ≤ g ⁻¹ᵁ U) (e' : V' ≤ g ⁻¹ᵁ U') (b : Γ(Y, U)) :
    (g.appLE U' V' e').hom ((Y.presheaf.map (homOfLE hU).op).hom b) =
      (X.presheaf.map (homOfLE hV).op).hom ((g.appLE U V e).hom b) := by
  have h1 := congrArg (fun φ => φ.hom b) (g.map_appLE e' (homOfLE hU).op)
  have h2 := congrArg (fun φ => φ.hom b) (g.appLE_map e (homOfLE hV).op)
  exact h1.trans h2.symm

lemma res_res (X : Scheme.{0}) {U V W : X.Opens} (i : V ⟶ U) (j : W ⟶ V) (k : W ⟶ U) (s : Γ(X, U)) :
    (X.presheaf.map j.op).hom ((X.presheaf.map i.op).hom s) = (X.presheaf.map k.op).hom s := by
  have := congrArg (fun φ => φ.hom s) (X.presheaf.map_comp i.op j.op)
  exact this.symm.trans rfl

theorem isPullback_app_of_isBasis : ∀ (Y₀ Y₁ Y₂ Y : Scheme.{0}) (i₁ : Y₀ ⟶ Y₁) (i₂ : Y₀ ⟶ Y₂) (j₁ : Y₁ ⟶ Y) (j₂ : Y₂ ⟶ Y) (hw : i₁ ≫ j₁ = i₂ ≫ j₂) (𝒱 : Set Y.Opens), TopologicalSpace.Opens.IsBasis 𝒱 → (∀ V ∈ 𝒱, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl))) → ∀ V : Y.Opens, IsPullback (j₁.app V) (j₂.app V) (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl) (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (by rw [hw]; exact le_rfl)) := by
  intro Y₀ Y₁ Y₂ Y i₁ i₂ j₁ j₂ hw 𝒱 h𝒱 hP
  have hle : ∀ V : Y.Opens, (i₁ ≫ j₁) ⁻¹ᵁ V ≤ i₂ ⁻¹ᵁ (j₂ ⁻¹ᵁ V) := fun V => by rw [hw]; exact le_rfl
  have hcomm : ∀ V : Y.Opens, j₁.app V ≫ i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl =
      j₂.app V ≫ i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V) := by
    intro V
    have key : ∀ (k k' : Y₀ ⟶ Y), k = k' → ∀ (e : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k ⁻¹ᵁ V)
        (e' : (i₁ ≫ j₁) ⁻¹ᵁ V ≤ k' ⁻¹ᵁ V), k.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e = k'.appLE V ((i₁ ≫ j₁) ⁻¹ᵁ V) e' := by
      rintro k _ rfl e e'; rfl
    exact (Scheme.Hom.comp_appLE i₁ j₁ V _ le_rfl).symm.trans
      ((key _ _ hw _ _).trans (Scheme.Hom.comp_appLE i₂ j₂ V _ (hle V)))
  have hcovY : ∀ U : Y.Opens, U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, W.1 := by
    intro U y hy
    obtain ⟨W, hW, hyW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 hy
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hyW⟩
  have hcov : ∀ {Z : Scheme.{0}} (f : Z ⟶ Y) (U : Y.Opens),
      f ⁻¹ᵁ U ≤ ⨆ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U}, f ⁻¹ᵁ W.1 := by
    intro Z f U z hz
    obtain ⟨W, hW, hzW, hWU⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 h𝒱 (x := f z) hz
    exact TopologicalSpace.Opens.mem_iSup.2 ⟨⟨W, hW, hWU⟩, hzW⟩

  have inj : ∀ (U : Y.Opens) (s t : Γ(Y, U)), (j₁.app U).hom s = (j₁.app U).hom t →
      (j₂.app U).hom s = (j₂.app U).hom t → s = t := by
    intro U s t h₁ h₂
    refine Y.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ U} => W.1) U
      (fun W => homOfLE W.2.2) (hcovY U) s t ?_
    rintro ⟨W, hW, hWU⟩
    obtain ⟨hinj, -⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
    apply hinj
    · exact (app_res j₁ (homOfLE hWU) s).trans ((congrArg _ h₁).trans (app_res j₁ (homOfLE hWU) t).symm)
    · exact (app_res j₂ (homOfLE hWU) s).trans ((congrArg _ h₂).trans (app_res j₂ (homOfLE hWU) t).symm)

  have surj : ∀ (V : Y.Opens) (b : Γ(Y₁, j₁ ⁻¹ᵁ V)) (c : Γ(Y₂, j₂ ⁻¹ᵁ V)),
      (i₁.appLE (j₁ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) le_rfl).hom b =
        (i₂.appLE (j₂ ⁻¹ᵁ V) ((i₁ ≫ j₁) ⁻¹ᵁ V) (hle V)).hom c →
      ∃ a, (j₁.app V).hom a = b ∧ (j₂.app V).hom a = c := by
    intro V b c hbc
    have loc : ∀ W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V}, ∃ a : Γ(Y, W.1),
        (j₁.app W.1).hom a = (Y₁.presheaf.map (homOfLE (j₁.preimage_mono W.2.2)).op).hom b ∧
        (j₂.app W.1).hom a = (Y₂.presheaf.map (homOfLE (j₂.preimage_mono W.2.2)).op).hom c := by
      rintro ⟨W, hW, hWV⟩
      obtain ⟨-, hex⟩ := (isPullback_iff_elem _ _ _ _ (hcomm W)).1 (hP W hW)
      apply hex
      have e1 := appLE_res i₁ (j₁.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) le_rfl le_rfl b
      have e2 := appLE_res i₂ (j₂.preimage_mono hWV) ((i₁ ≫ j₁).preimage_mono hWV) (hle V) (hle W) c
      exact e1.trans ((congrArg _ hbc).trans e2.symm)
    choose sf hsf₁ hsf₂ using loc
    have hcompat : TopCat.Presheaf.IsCompatible Y.sheaf.1 (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) sf := by
      intro W W'
      apply inj
      · refine (app_res j₁ _ _).trans (Eq.trans ?_ (app_res j₁ _ _).symm)
        rw [hsf₁, hsf₁]
        exact (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).trans
          (res_res Y₁ _ _ (homOfLE (j₁.preimage_mono (inf_le_left.trans W.2.2))) b).symm
      · refine (app_res j₂ _ _).trans (Eq.trans ?_ (app_res j₂ _ _).symm)
        rw [hsf₂, hsf₂]
        exact (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).trans
          (res_res Y₂ _ _ (homOfLE (j₂.preimage_mono (inf_le_left.trans W.2.2))) c).symm
    obtain ⟨s, hs, -⟩ := Y.sheaf.existsUnique_gluing' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => W.1) V
      (fun W => homOfLE W.2.2) (hcovY V) sf hcompat
    refine ⟨s, ?_, ?_⟩
    · refine Y₁.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₁ ⁻¹ᵁ W.1) (j₁ ⁻¹ᵁ V)
        (fun W => homOfLE (j₁.preimage_mono W.2.2)) (hcov j₁ V) _ _ ?_
      intro W
      exact (app_res j₁ (homOfLE W.2.2) s).symm.trans ((congrArg (j₁.app W.1).hom (hs W)).trans (hsf₁ W))
    · refine Y₂.sheaf.eq_of_locally_eq' (fun W : {W : Y.Opens // W ∈ 𝒱 ∧ W ≤ V} => j₂ ⁻¹ᵁ W.1) (j₂ ⁻¹ᵁ V)
        (fun W => homOfLE (j₂.preimage_mono W.2.2)) (hcov j₂ V) _ _ ?_
      intro W
      exact (app_res j₂ (homOfLE W.2.2) s).symm.trans ((congrArg (j₂.app W.1).hom (hs W)).trans (hsf₂ W))
  intro V
  exact (isPullback_iff_elem _ _ _ _ (hcomm V)).2 ⟨fun x y hx hy => inj V x y hx hy, surj V⟩

end GlobalTheory.PinchBasis
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedFieldTensorIntFiniteReduced
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory.FinRedTensor

theorem formallyUnramified_int_of_finite_field (K : Type) [Field K] [Finite K] :
    Algebra.FormallyUnramified ℤ K := by
  obtain ⟨p, hp⟩ := CharP.exists K
  haveI : NeZero p := ⟨CharP.char_ne_zero_of_finite K p⟩
  haveI : Fact p.Prime := CharP.char_is_prime_of_pos K p
  letI : Algebra (ZMod p) K := ZMod.algebra K p
  haveI : Module.Finite (ZMod p) K := Module.Finite.of_finite
  haveI : Algebra.IsSeparable (ZMod p) K := inferInstance
  haveI : Algebra.FormallyUnramified (ZMod p) K := Algebra.FormallyUnramified.of_isSeparable _ _
  haveI : Algebra.FormallyUnramified ℤ (ZMod p) :=
    Algebra.FormallyUnramified.of_surjective (Algebra.ofId ℤ (ZMod p)) (ZMod.intCast_surjective)
  exact Algebra.FormallyUnramified.comp ℤ (ZMod p) K

theorem formallyUnramified_int_of_finite_isReduced (A : Type) [CommRing A] [Finite A]
    [IsReduced A] : Algebra.FormallyUnramified ℤ A := by
  haveI : IsArtinianRing A := inferInstance
  have h : Algebra.FormallyUnramified ℤ (∀ I : MaximalSpectrum A, A ⧸ I.asIdeal) := by
    rw [Algebra.FormallyUnramified.pi_iff]
    intro I
    have := I.isMaximal
    letI := Ideal.Quotient.field I.asIdeal
    haveI : Finite (A ⧸ I.asIdeal) :=
      Finite.of_surjective (Ideal.Quotient.mk I.asIdeal) Ideal.Quotient.mk_surjective
    exact formallyUnramified_int_of_finite_field _
  exact Algebra.FormallyUnramified.of_equiv ((IsArtinianRing.equivPi A).restrictScalars ℤ).symm

theorem isReduced_field_tensor_finite :
    ∀ (A : Type) [CommRing A] [Finite A] [IsReduced A] (k : Type) [Field k],
      IsReduced (k ⊗[ℤ] A) := by
  intro A _ _ _ k _
  haveI := formallyUnramified_int_of_finite_isReduced A
  haveI : Algebra.FormallyUnramified k (k ⊗[ℤ] A) := Algebra.FormallyUnramified.base_change k
  haveI : Module.Finite ℤ A := Module.Finite.of_finite
  haveI : Algebra.EssFiniteType k (k ⊗[ℤ] A) := inferInstance
  exact Algebra.FormallyUnramified.isReduced_of_field k _

end GlobalTheory.FinRedTensor
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsReducedQuotTensorOfReducedModP
section
open NumberField
open scoped TensorProduct

namespace GlobalTheory

theorem reduced_quot_tensor_of_reduced_modp :
    ∀ (O : Type) [CommRing O] (k : Type) [Field k] (p : ℕ) (ϖ : O), (p : k) = 0 →
      IsReduced (k ⊗[ℤ] (O ⧸ Ideal.span {(p : O), ϖ})) →
      IsReduced ((k ⊗[ℤ] O) ⧸ Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ}) := by
  intro O _ k _ p ϖ hp hred
  set I : Ideal O := Ideal.span {(p : O), ϖ}
  set f := Algebra.TensorProduct.map (AlgHom.id ℤ k) (Ideal.Quotient.mkₐ ℤ I) with hf
  have hker : RingHom.ker f.toRingHom = Ideal.span {(1 : k) ⊗ₜ[ℤ] ϖ} := by
    have h := Algebra.TensorProduct.lTensor_ker (A := k) (Ideal.Quotient.mkₐ ℤ I)
      (Ideal.Quotient.mkₐ_surjective ℤ I)
    have hk : RingHom.ker (Ideal.Quotient.mkₐ ℤ I) = I := Ideal.Quotient.mkₐ_ker ℤ I
    have h0 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) (p : O) = 0 := by
      rw [map_natCast]
      have : ((p : ℕ) : k ⊗[ℤ] O) = (Algebra.TensorProduct.includeLeft : k →ₐ[ℤ] k ⊗[ℤ] O) (p : k) := by
        rw [map_natCast]
      rw [this, hp, map_zero]
    have h1 : (Algebra.TensorProduct.includeRight : O →ₐ[ℤ] k ⊗[ℤ] O) ϖ = (1 : k) ⊗ₜ[ℤ] ϖ := rfl
    have e := h
    rw [hk] at e
    change RingHom.ker f.toRingHom = _ at e
    rw [e, Ideal.map_span, Set.image_pair]
    erw [h0, h1]
    exact Ideal.span_insert_zero
  have hinj : Function.Injective (RingHom.kerLift f.toRingHom) := RingHom.kerLift_injective _
  have hR : IsReduced (k ⊗[ℤ] O ⧸ RingHom.ker f.toRingHom) := isReduced_of_injective _ hinj
  rw [hker] at hR
  exact hR

end GlobalTheory
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsRegFamConst
section
noncomputable section

namespace GlobalTheory.CuspDbl

open Metric

def IsRegFam {Y : Type} [TopologicalSpace Y] (ht : Y → ℝ) (s₀ : ℂ) (Ez : ℂ → Y → Y → ℂ) : Prop :=
  ∀ s₁ : ℂ, ∃ (k : ℕ) (r C : ℝ) (N : ℕ) (Hf : ℂ → Y → Y → ℂ), 0 < r ∧ (s₁ = s₀ → k = 0) ∧
    (∀ s ∈ ball s₁ r, (s ≠ s₁ ∨ k = 0) → ∀ h h', Hf s h h' = (s - s₁) ^ k * Ez s h h') ∧
    (∀ h h', DifferentiableOn ℂ (Hf · h h') (ball s₁ r)) ∧
    (∀ s ∈ ball s₁ r, Continuous fun x : Y × Y => Hf s x.1 x.2) ∧
    ∀ s ∈ ball s₁ r, ∀ h h', ‖Hf s h h'‖ ≤ C * (ht h * ht h') ^ N

end GlobalTheory.CuspDbl

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsTorsionFreeRingOfIntegersOfIsTorsionFreeInt
section
open NumberField

namespace GlobalTheory

theorem isTorsionFree_ringOfIntegers_of_isTorsionFree_int (E : Type) [Field E] [NumberField E]
    (N : Type) [AddCommGroup N] [Module (𝓞 E) N] [Module.IsTorsionFree ℤ N] :
    Module.IsTorsionFree (𝓞 E) N := by
  refine Module.IsTorsionFree.of_smul_eq_zero (fun c x hcx => ?_)
  by_cases hc : c = 0
  · exact Or.inl hc
  · right
    have halg : IsAlgebraic ℤ c := (Algebra.IsIntegral.isIntegral (R := ℤ) c).isAlgebraic
    obtain ⟨m, hm, d, hd⟩ := halg.exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)
    have h1 : m • x = 0 := by
      rw [← Int.cast_smul_eq_zsmul (𝓞 E)]
      have : ((m : ℤ) : 𝓞 E) = d * c := by
        rw [mul_comm, ← hd]; simp
      rw [this, mul_smul, hcx, smul_zero]
    exact (smul_eq_zero.mp h1).resolve_left hm

end GlobalTheory
end

