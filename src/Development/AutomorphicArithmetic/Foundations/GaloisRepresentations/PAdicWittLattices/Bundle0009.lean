import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.Bundle0004

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.POrdEx
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry

namespace UpperTheory.Gal.G3

private theorem ordExStep (hS : OrdStep) {Z Y W : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s] (d : ℕ)
    (c : W ⟶ Z) (σ : Fin d → (W ⟶ Y)) (hcf : IsFinite c) (hce : Etale c) (hσ : ∀ j, σ j ≫ s = c)
    (hinj : ∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W), Function.Injective fun j => x ≫ σ j)
    (huniv : ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin d → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
      ∃! w : U ⟶ W, w ≫ c = z ∧ ∀ j, w ≫ σ j = y j) :
    ∃ (W' : Scheme.{0}) (c' : W' ⟶ Z) (σ' : Fin (d + 1) → (W' ⟶ Y)), IsFinite c' ∧ Etale c' ∧
      (∀ j, σ' j ≫ s = c') ∧
      (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ W'), Function.Injective fun j => x ≫ σ' j) ∧
      ∀ (U : Scheme.{0}) (z : U ⟶ Z) (y : Fin (d + 1) → (U ⟶ Y)), (∀ j, y j ≫ s = z) →
        (∀ (Ω : Type) [Field Ω] (x : sp Ω ⟶ U), Function.Injective fun j => x ≫ y j) →
        ∃! w : U ⟶ W', w ≫ c' = z ∧ ∀ j, w ≫ σ' j = y j := by
  haveI := hcf
  haveI := hce
  let P := pullback s c
  have hsq : ∀ j, σ j ≫ s = 𝟙 W ≫ c := fun j => by rw [hσ j, Category.id_comp]
  let sec : Fin d → (W ⟶ P) := fun j => pullback.lift (σ j) (𝟙 W) (hsq j)
  have hsec1 : ∀ j, sec j ≫ pullback.fst s c = σ j := fun j => pullback.lift_fst _ _ _
  have hsec2 : ∀ j, sec j ≫ pullback.snd s c = 𝟙 W := fun j => pullback.lift_snd _ _ _
  haveI hOP : MorphismProperty.HasOfPostcompProperty (@IsOpenImmersion : MorphismProperty Scheme)
      (@Etale : MorphismProperty Scheme) := by
    apply MorphismProperty.hasOfPostcompProperty_iff_le_diagonal.2
    intro X Y f hf
    haveI : Etale f := hf
    exact inferInstanceAs <| IsOpenImmersion (pullback.diagonal f)
  have hopen : ∀ j, IsOpenImmersion (sec j) := fun j =>
    MorphismProperty.of_postcomp (W := (@IsOpenImmersion : MorphismProperty Scheme))
      (W' := (@Etale : MorphismProperty Scheme)) (sec j) (pullback.snd s c)
      (inferInstanceAs (Etale (pullback.snd s c)))
      (by rw [hsec2]; exact inferInstanceAs (IsOpenImmersion (𝟙 W)))
  have hclosed : ∀ j, IsClosedImmersion (sec j) := fun j => by
    haveI : IsClosedImmersion (sec j ≫ pullback.snd s c) := by
      rw [hsec2]; infer_instance
    exact IsClosedImmersion.of_comp (sec j) (pullback.snd s c)
  let S : Set P := ⋃ j, Set.range (sec j).base
  have hSc : IsClosed S := isClosed_iUnion_of_finite fun j => (hclosed j).isClosedEmbedding.isClosed_range
  have hSo : IsOpen S := isOpen_iUnion fun j => (hopen j).base_open.isOpen_range
  let O : P.Opens := ⟨Sᶜ, hSc.isOpen_compl⟩
  have hOr : Set.range O.ι.base = Sᶜ := O.range_ι
  haveI : IsClosedImmersion O.ι := .of_isPreimmersion _ (by rw [hOr]; exact hSo.isClosed_compl)
  have hpt : ∀ (j : Fin d) (Ω : Type) [Field Ω] (x : sp Ω ⟶ P),
      x.base (IsLocalRing.closedPoint Ω) ∈ Set.range (sec j).base →
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j := by
    intro j Ω _ x hx
    have hr : Set.range x.base ⊆ Set.range (sec j).base := by
      rintro _ ⟨p, rfl⟩
      rwa [Subsingleton.elim p (IsLocalRing.closedPoint Ω)]
    haveI := hopen j
    have hf := IsOpenImmersion.lift_fac (sec j) x hr
    rw [← hf, Category.assoc, Category.assoc, hsec1, reassoc_of% hsec2]
  have hback : ∀ (j : Fin d) {T : Scheme.{0}} (x : T ⟶ P),
      x ≫ pullback.fst s c = x ≫ pullback.snd s c ≫ σ j → x = (x ≫ pullback.snd s c) ≫ sec j := by
    intro j T x hx
    apply pullback.hom_ext
    · rw [Category.assoc, hsec1, hx, Category.assoc]
    · rw [Category.assoc, hsec2, Category.comp_id]
  refine ⟨O, O.ι ≫ pullback.snd s c ≫ c,
    Fin.snoc (α := fun _ => ((O : Scheme) ⟶ Y)) (fun j => O.ι ≫ pullback.snd s c ≫ σ j)
      (O.ι ≫ pullback.fst s c), inferInstance, inferInstance, ?_, ?_, ?_⟩
  · intro k
    refine Fin.lastCases ?_ (fun j => ?_) k
    · simp only [Fin.snoc_last, Category.assoc, pullback.condition]
    · simp only [Fin.snoc_castSucc, Category.assoc, hσ j]
  · intro Ω _ x
    have key : ∀ j : Fin d, x ≫ O.ι ≫ pullback.fst s c ≠ x ≫ O.ι ≫ pullback.snd s c ≫ σ j := by
      intro j h
      have h2 := hback j (x ≫ O.ι) (by simpa only [Category.assoc] using h)
      have hin : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ S := by
        rw [h2]
        exact Set.mem_iUnion.2 ⟨j, _, rfl⟩
      have hO : (x ≫ O.ι).base (IsLocalRing.closedPoint Ω) ∈ Set.range O.ι.base :=
        ⟨x.base (IsLocalRing.closedPoint Ω), rfl⟩
      rw [hOr] at hO
      exact hO hin
    intro a b hab
    simp only at hab
    induction a using Fin.lastCases with
    | last =>
      induction b using Fin.lastCases with
      | last => rfl
      | cast j =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab (key j)
    | cast i =>
      induction b using Fin.lastCases with
      | last =>
        simp only [Fin.snoc_last, Fin.snoc_castSucc] at hab
        exact absurd hab.symm (key i)
      | cast j =>
        simp only [Fin.snoc_castSucc] at hab
        exact congrArg Fin.castSucc (hinj Ω (x ≫ O.ι ≫ pullback.snd s c) (by simpa only [Category.assoc] using hab))
  · intro U z y hy hinjU
    obtain ⟨w0, ⟨hw0c, hw0σ⟩, hw0u⟩ := huniv U z (fun j => y j.castSucc) (fun j => hy _)
      (fun Ω _ x a b h => Fin.castSucc_injective _ (hinjU Ω x h))
    let φ : U ⟶ P := pullback.lift (y (Fin.last d)) w0 (by rw [hy, hw0c])
    have hφ1 : φ ≫ pullback.fst s c = y (Fin.last d) := pullback.lift_fst _ _ _
    have hφ2 : φ ≫ pullback.snd s c = w0 := pullback.lift_snd _ _ _
    have hrange : Set.range φ.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨u, rfl⟩
      rw [hOr]
      intro hu
      obtain ⟨j, hj⟩ := Set.mem_iUnion.1 hu
      let x := U.fromSpecResidueField u
      have hxu : x.base (IsLocalRing.closedPoint (U.residueField u)) = u :=
        U.fromSpecResidueField_apply u _
      have := hpt j (U.residueField u) (x ≫ φ) (by
        show φ.base (x.base _) ∈ _
        rw [hxu]
        exact hj)
      rw [Category.assoc, Category.assoc, hφ1, reassoc_of% hφ2, hw0σ] at this
      exact (Fin.castSucc_lt_last j).ne (hinjU _ x this).symm
    refine ⟨IsOpenImmersion.lift O.ι φ hrange, ⟨?_, fun k => ?_⟩, ?_⟩
    · rw [IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0c]
    · refine Fin.lastCases ?_ (fun j => ?_) k
      · rw [Fin.snoc_last, IsOpenImmersion.lift_fac_assoc, hφ1]
      · rw [Fin.snoc_castSucc, IsOpenImmersion.lift_fac_assoc, reassoc_of% hφ2, hw0σ]
    · rintro w' ⟨hw'c, hw'σ⟩
      rw [← cancel_mono O.ι, IsOpenImmersion.lift_fac]
      have e2 : w' ≫ O.ι ≫ pullback.snd s c = w0 := by
        refine hw0u _ ⟨by simpa only [Category.assoc] using hw'c, fun j => ?_⟩
        have := hw'σ j.castSucc
        rw [Fin.snoc_castSucc] at this
        simpa only [Category.assoc] using this
      apply pullback.hom_ext
      · have := hw'σ (Fin.last d)
        rw [Fin.snoc_last] at this
        rw [Category.assoc, this, hφ1]
      · rw [Category.assoc, e2, hφ2]

theorem pOrdEx : OrdStep → OrdEx := by
  intro hS Z Y s _ _ d
  induction d with
  | zero =>
    refine ⟨Z, 𝟙 Z, Fin.elim0, inferInstance, inferInstance, fun j => j.elim0, ?_, ?_⟩
    · intro Ω _ x a
      exact a.elim0
    · intro U z y _ _
      exact ⟨z, ⟨Category.comp_id _, fun j => j.elim0⟩, fun w hw => by simpa using hw.1⟩
  | succ d ih =>
    obtain ⟨W, c, σ, hcf, hce, hσ, hinj, huniv⟩ := ih
    exact ordExStep hS s d c σ hcf hce hσ hinj huniv

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PPtsOfSplits
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem sp_subsingleton (Ω : Type) [Field Ω] : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) :=
  inferInstanceAs (Subsingleton (PrimeSpectrum Ω))

private theorem exists_factor_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω]
    (u : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), x ≫ Sigma.ι (fun _ : J => W) j = u := by
  haveI := sp_subsingleton Ω
  have p : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (u p) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = u p := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) u ?_,
    IsOpenImmersion.lift_fac _ _ _⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = p := Subsingleton.elim _ _
  exact ⟨y, hy⟩

private theorem index_eq_of_ι {J : Type} {W : Scheme.{0}} (Ω : Type) [Field Ω] {j j' : J}
    {x x' : UpperTheory.Gal.G3.sp Ω ⟶ W}
    (h : x ≫ Sigma.ι (fun _ : J => W) j = x' ≫ Sigma.ι (fun _ : J => W) j') : j = j' := by
  by_contra hne
  have he := isEmpty_of_commSq_sigmaι_of_ne (g := fun _ : J => W) ⟨h⟩ hne
  exact he.false (show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩)

theorem UpperTheory.Gal.G3.pPtsOfSplits :
    PtsOfSplits := by
  intro Z Y W s c J σ hs Ω _ x y hxy
  obtain ⟨hσ, hiso⟩ := hs
  haveI := hiso
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  obtain ⟨j, x', hx'⟩ := exists_factor_ι Ω (pullback.lift y x hxy ≫ inv e)
  have h1 : x' ≫ Sigma.ι (fun _ : J => W) j ≫ e = pullback.lift y x hxy := by
    rw [← Category.assoc, hx', Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  rw [hι] at h1
  have hsnd := congrArg (· ≫ pullback.snd s c) h1
  have hfst := congrArg (· ≫ pullback.fst s c) h1
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hsnd hfst
  rw [hsnd] at hfst
  refine ⟨j, hfst, fun j' hj' => ?_⟩
  have hj'' : x ≫ σ j' = y := hj'
  apply index_eq_of_ι Ω (x := x) (x' := x')
  rw [hx']
  apply (cancel_mono e).mp
  rw [Category.assoc, hι, Category.assoc, IsIso.inv_hom_id, Category.comp_id]
  apply pullback.hom_ext
  · rw [Category.assoc, pullback.lift_fst, pullback.lift_fst, hj'']
  · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, Category.comp_id]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsBasic
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.GalV

namespace UpperTheory.Gal.G3

private theorem splits_restrict (hS : SplitsPts) (hP : PtsOfSplits) {Z Y W W' : Scheme.{0}} (s : Y ⟶ Z) [IsFinite s] [Etale s]
    (c : W ⟶ Z) (J : Type) [Finite J] (σ : J → (W ⟶ Y)) (g : W' ⟶ W) (h : Splits s c σ) :
    Splits s (g ≫ c) fun j => g ≫ σ j := by
  have h0 := h
  obtain ⟨hc, -⟩ := h
  refine hS s (g ≫ c) J (fun j => g ≫ σ j) (fun j => by simp [hc j]) ?_
  intro Ω _ _ x y hy
  have hy' : y ≫ s = (x ≫ g) ≫ c := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s c J σ h0 Ω (x ≫ g) y hy'
  exact ⟨j, by simpa using hj, fun i hi => huniq i (by simpa using hi)⟩

private theorem splits_down (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s' c σ) : Splits s (c ≫ g) fun j => σ j ≫ v := by
  refine hS s (c ≫ g) J (fun j => σ j ≫ v)
    (fun j => by rw [Category.assoc, sq.w, ← Category.assoc, hσ j]) ?_
  intro Ω _ _ x y hy
  have hw : y ≫ s = (x ≫ c) ≫ g := by simpa using hy
  obtain ⟨j, hj, huniq⟩ := hP s' c J σ h Ω x (sq.lift y (x ≫ c) hw) (by simp)
  refine ⟨j, ?_, ?_⟩
  · simp only
    rw [← Category.assoc, hj, sq.lift_fst]
  · intro i hi
    apply huniq
    apply sq.hom_ext
    · simpa using hi
    · simp [hσ i]

private theorem splits_up (hS : SplitsPts) (hP : PtsOfSplits) {P Y Z' Z W : Scheme.{0}} {v : P ⟶ Y} {s' : P ⟶ Z'} {s : Y ⟶ Z}
    {g : Z' ⟶ Z} [IsFinite s] [Etale s] (sq : IsPullback v s' s g) (c : W ⟶ Z') (J : Type) [Finite J] (σ : J → (W ⟶ P))
    (hσ : ∀ j, σ j ≫ s' = c) (h : Splits s (c ≫ g) fun j => σ j ≫ v) : Splits s' c σ := by
  have : IsFinite s' := MorphismProperty.of_isPullback (P := @IsFinite) sq ‹_›
  have : Etale s' := MorphismProperty.of_isPullback (P := @Etale) sq ‹_›
  refine hS s' c J σ hσ ?_
  intro Ω _ _ x y hy
  have hw : (y ≫ v) ≫ s = x ≫ c ≫ g := by
    rw [Category.assoc, sq.w, ← Category.assoc, hy, Category.assoc]
  obtain ⟨j, hj, huniq⟩ := hP s (c ≫ g) J (fun j => σ j ≫ v) h Ω x (y ≫ v) hw
  refine ⟨j, ?_, ?_⟩
  · apply sq.hom_ext
    · simpa using hj
    · simp [hσ j, hy]
  · intro i hi
    apply huniq
    rw [← Category.assoc, hi]

theorem pSplitsBasic : SplitsPts → PtsOfSplits → SplitsBasic := fun hS hP =>
  ⟨fun s _ _ c J _ σ g h => splits_restrict hS hP s c J σ g h,
   fun _ _ _ _ _ _ sq c J _ σ hσ => ⟨splits_down hS hP sq c J σ hσ, splits_up hS hP sq c J σ hσ⟩⟩

end UpperTheory.Gal.G3

end
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsComp
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pSplitsComp :
    SplitsPts → PtsOfSplits → SplitsComp := by
  intro hS hP Y P Z W κ s _ _ _ _ c I J _ _ τ σ hτ hσ
  have hτc : ∀ i, τ i ≫ s = c := hτ.1
  have hσc : ∀ i j, σ i j ≫ κ = τ i := fun i => (hσ i).1
  refine hS (κ ≫ s) c (I × J) (fun x => σ x.1 x.2)
    (fun x => by rw [← Category.assoc, hσc, hτc]) ?_
  intro Ω _ _ x y hy
  obtain ⟨i, hi, hiu⟩ := hP s c I τ hτ Ω x (y ≫ κ) (by simpa using hy)
  obtain ⟨j, hj, hju⟩ := hP κ (τ i) J (σ i) (hσ i) Ω x y hi.symm
  refine ⟨(i, j), hj, ?_⟩
  rintro ⟨i', j'⟩ h'
  have h'' : x ≫ σ i' j' = y := h'
  have hi' : i' = i := hiu i' (by
    show x ≫ τ i' = y ≫ κ
    rw [← hσc i' j', ← Category.assoc, h''])
  subst hi'
  have hj' : j' = j := hju j' h''
  subst hj'
  rfl
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PSplitsPts
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem exists_factor {W : Scheme.{0}} {J : Type} (Ω : Type) [Field Ω]
    (p : UpperTheory.Gal.G3.sp Ω ⟶ ∐ (fun _ : J => W)) :
    ∃ (j : J) (x : UpperTheory.Gal.G3.sp Ω ⟶ W), p = x ≫ Sigma.ι (fun _ : J => W) j := by
  haveI : Subsingleton ↑(UpperTheory.Gal.G3.sp Ω) := inferInstanceAs (Subsingleton (PrimeSpectrum Ω))
  have pt : ↑(UpperTheory.Gal.G3.sp Ω) := show PrimeSpectrum Ω from ⟨⊥, Ideal.bot_prime⟩
  obtain ⟨⟨j, y⟩, hq⟩ : ∃ q, (sigmaMk (fun _ : J => W)).symm (p pt) = q := ⟨_, rfl⟩
  have hy : Sigma.ι (fun _ : J => W) j y = p pt := by
    rw [← sigmaMk_mk, ← hq, Homeomorph.apply_symm_apply]
  refine ⟨j, IsOpenImmersion.lift (Sigma.ι (fun _ : J => W) j) p ?_,
    (IsOpenImmersion.lift_fac _ _ _).symm⟩
  rintro _ ⟨z, rfl⟩
  obtain rfl : z = pt := Subsingleton.elim _ _
  exact ⟨y, hy⟩

theorem UpperTheory.Gal.G3.pSplitsPts :
    IsoPts → SplitsPts := by
  intro hIso Z Y W s _ _ c J _ σ hσ hpts
  refine ⟨hσ, ?_⟩
  let e := Limits.Sigma.desc (fun j : J =>
    pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j))
  have hι : ∀ j, Sigma.ι (fun _ : J => W) j ≫ e =
      pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) :=
    fun j => Sigma.ι_desc _ _
  have hlift : ∀ j, Etale (pullback.lift (σ j) (𝟙 W)
      (by rw [Category.id_comp]; exact hσ j) : W ⟶ pullback s c) := by
    intro j
    haveI : Etale (pullback.lift (σ j) (𝟙 W) (by rw [Category.id_comp]; exact hσ j) ≫
        pullback.snd s c) := by
      rw [pullback.lift_snd]; infer_instance
    exact Etale.of_comp _ (pullback.snd s c)
  haveI : IsZariskiLocalAtSource @Etale :=
    HasRingHomProperty.instIsZariskiLocalAtSource (Q := RingHom.Etale)
  haveI : Etale e := IsZariskiLocalAtSource.sigmaDesc (P := @Etale) hlift
  show IsIso e
  apply hIso e
  intro Ω _ _ z
  obtain ⟨j, hj, huniq⟩ := hpts Ω (z ≫ pullback.snd s c) (z ≫ pullback.fst s c)
    (by rw [Category.assoc, Category.assoc, pullback.condition])
  have hz : (z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j ≫ e = z := by
    rw [hι]
    apply pullback.hom_ext
    · simp only [Category.assoc, pullback.lift_fst]
      rw [← Category.assoc]
      exact hj
    · simp only [Category.assoc, pullback.lift_snd, Category.comp_id]
  refine ⟨(z ≫ pullback.snd s c) ≫ Sigma.ι (fun _ : J => W) j,
    by rw [Category.assoc]; exact hz, fun q hq => ?_⟩
  obtain ⟨j', x', rfl⟩ := exists_factor Ω q
  rw [Category.assoc, hι] at hq
  have hs := congrArg (· ≫ pullback.snd s c) hq
  have hf := congrArg (· ≫ pullback.fst s c) hq
  simp only [Category.assoc, pullback.lift_fst, pullback.lift_snd, Category.comp_id] at hs hf
  have hjj : j' = j := huniq j' (by rw [← hs]; exact hf)
  rw [hjj, hs]
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrBase
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrBase :
    FEtBasic → SplitsBasic → GalClosD → TrBase.{u} := by
  intro hF hS hC B R _ T hT P Y Z' Z p q p' q' v s' s g d hv hg hq' hpb hs tr tr' htr htr' x
  haveI : IsFinite s := hs.1
  haveI : Etale s := hs.2.1
  obtain ⟨W, c, G, _, _, a, σ, hgal, hspl⟩ := hC s' d (hF.1 v s' s g d hpb hs)
  have hσs : ∀ j, σ j ≫ s' = c := hspl.1
  have hσ' : ∀ j, σ j ≫ q' = c ≫ p' := fun j => by
    rw [← hq', ← Category.assoc, hσs j]
  have hσv : ∀ j, (σ j ≫ v) ≫ q = c ≫ p' := fun j => by
    rw [Category.assoc, hv, hσ' j]
  have hcg : (c ≫ g) ≫ p = c ≫ p' := by rw [Category.assoc, hg]
  have hspl2 : Splits s (c ≫ g) (fun j => σ j ≫ v) :=
    (hS.2 v s' s g hpb c (Fin d) σ hσs).1 hspl
  apply hT.inj p' (c ≫ p') c rfl G a hgal
  rw [← T.pull_comp c g rfl hg hcg, htr W (c ≫ p') (c ≫ g) hcg (Fin d) (fun j => σ j ≫ v) hσv hspl2 x,
    htr' W (c ≫ p') c rfl (Fin d) σ hσ' hspl]
  refine Finset.sum_congr rfl fun j _ => ?_
  exact T.pull_comp (σ j) v (hσ' j) hv (hσv j) x
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PTrPushM
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

theorem UpperTheory.Gal.G3.pTrPushM :
    FEtBasic → SplitsBasic → SplitsComp → MultiSplit → FEtInj.{u} → TrPushM.{u} := by
  intro hF hSB hSC hMS hInj B R _ T hT Y P Z p q r κ s d m hκ hs hd hm tr tr' htr htr' x
  haveI : IsFinite s := hd.1
  haveI : Etale s := hd.2.1
  haveI : IsFinite κ := hm.1
  haveI : Etale κ := hm.2.1
  obtain ⟨W1, c1, e1, he1, hc1, hτ0⟩ := hMS 1 (fun _ => P) (fun _ => s) (fun _ => d) (fun _ => hd)
  obtain ⟨τ, hτ⟩ : ∃ τ : Fin d → (W1 ⟶ P), Splits s c1 τ := hτ0 0
  have hPb : ∀ i : Fin d, FEt (pullback.snd κ (τ i)) m := fun i =>
    hF.1 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i) m
      (IsPullback.of_hasPullback κ (τ i)) hm
  obtain ⟨W2, c2, e2, he2, hc2, hρ0⟩ :=
    hMS d (fun i => pullback κ (τ i)) (fun i => pullback.snd κ (τ i)) (fun _ => m) hPb
  have hρ1 : ∀ i : Fin d, ∃ ρ : Fin m → (W2 ⟶ pullback κ (τ i)),
      Splits (pullback.snd κ (τ i)) c2 ρ := hρ0
  choose ρ hρ using hρ1
  have key : ∀ i j, (ρ i j ≫ pullback.fst κ (τ i)) ≫ κ = c2 ≫ τ i := fun i j => by
    rw [Category.assoc, pullback.condition, ← Category.assoc, (hρ i).1 j]
  have hsκ : ∀ i, Splits κ (c2 ≫ τ i) (fun j => ρ i j ≫ pullback.fst κ (τ i)) := fun i =>
    (hSB.2 (pullback.fst κ (τ i)) (pullback.snd κ (τ i)) κ (τ i)
      (IsPullback.of_hasPullback κ (τ i)) c2 (Fin m) (ρ i) (hρ i).1).1 (hρ i)
  have hss : Splits s (c2 ≫ c1) (fun i => c2 ≫ τ i) := hSB.1 s c1 (Fin d) τ c2 hτ
  have hcomp := hSC κ s (c2 ≫ c1) (Fin d) (Fin m) (fun i => c2 ≫ τ i)
    (fun i j => ρ i j ≫ pullback.fst κ (τ i)) hss hsκ
  have hfc : FEt (c2 ≫ c1) (e1 * e2) := hF.2.1 c2 c1 e1 e2 hc2 hc1
  have hστ : ∀ i, (c2 ≫ τ i) ≫ q = (c2 ≫ c1) ≫ p := fun i => by
    rw [← hs]
    simp only [Category.assoc]
    rw [← Category.assoc (τ i) s p, hτ.1 i]
  have hσ' : ∀ y : Fin d × Fin m, (ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) ≫ r = (c2 ≫ c1) ≫ p :=
    fun y => by
      rw [← hκ, ← Category.assoc, key]
      exact hστ y.1
  have move : ∀ (f : W2 ⟶ Y) (g : W2 ⟶ P) (hf : f ≫ r = (c2 ≫ c1) ≫ p)
      (hg : g ≫ q = (c2 ≫ c1) ≫ p), f ≫ κ = g → T.pull f hf (T.pull κ hκ x) = T.pull g hg x := by
    intro f g hf hg e
    subst e
    exact (T.pull_comp f κ hf hκ hg x).symm
  apply hInj T hT p ((c2 ≫ c1) ≫ p) (c2 ≫ c1) rfl (e1 * e2) (Nat.mul_pos he1 he2) hfc
  rw [htr' W2 _ (c2 ≫ c1) rfl (Fin d × Fin m) (fun y => ρ y.1 y.2 ≫ pullback.fst κ (τ y.1)) hσ' hcomp]
  rw [map_smul, htr W2 _ (c2 ≫ c1) rfl (Fin d) (fun i => c2 ≫ τ i) hστ hss]
  rw [Fintype.sum_prod_type, Finset.smul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_congr rfl fun j _ => move _ _ (hσ' (i, j)) (hστ i) (key i j)]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  exact (Nat.cast_smul_eq_nsmul R m _).symm
end

-- bundled from Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.PAdicWittLattices.PullIdentityMove
section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC GlobalTheory.GalV GlobalTheory.HodgeCoh TensorProduct UpperTheory.Gal.G3
open UpperTheory.Gal.Int.Geo (FEt Cover gen piece IsHEig)
universe u v

private theorem pullIdentity_move {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {W Z Z' : Scheme.{0}}
    {p : Z ⟶ B} {p' : Z' ⟶ B} {r r' : W ⟶ B} (e : r = r') (c : W ⟶ Z) {J : Type} [Fintype J]
    (t : J → (W ⟶ Z')) (y : T.H p) (x : T.H p') (h : c ≫ p = r) (h' : c ≫ p = r')
    (k : ∀ j, t j ≫ p' = r) (k' : ∀ j, t j ≫ p' = r')
    (H : T.pull c h y = ∑ j, T.pull (t j) (k j) x) :
    T.pull c h' y = ∑ j, T.pull (t j) (k' j) x := by
  subst e
  exact H

private theorem pull_congr {B : Scheme.{0}} {R : Type} [Field R] (T : Th.{u} B R) {X Y : Scheme.{0}}
    {p : X ⟶ B} {q : Y ⟶ B} {f f' : Y ⟶ X} (e : f = f') (h : f ≫ p = q) (h' : f' ≫ p = q) (x : T.H p) :
    T.pull f h x = T.pull f' h' x := by
  subst e
  rfl

private theorem bcMap_comp' {B B' X Y V : Scheme.{0}} (g : B ⟶ B') {p : X ⟶ B'} {q : Y ⟶ B'} {r : V ⟶ B'}
    (f : Y ⟶ X) (f' : V ⟶ Y) (h : f ≫ p = q) (h' : f' ≫ q = r) (h'' : (f' ≫ f) ≫ p = r) :
    bcMap g (f' ≫ f) h'' = bcMap g f' h' ≫ bcMap g f h := by
  apply pullback.hom_ext
  · rw [bcMap_fst, Category.assoc, bcMap_fst, ← Category.assoc (bcMap g f' h'), bcMap_fst,
      Category.assoc]
  · rw [bcMap_snd, Category.assoc, bcMap_snd, bcMap_snd]

theorem UpperTheory.Gal.G3.pOpBc :
    BcSplits → BcGal → OpBc.{u} := by
  intro hS hG B B' R _ T g Z Y Z' p q p' s _ _ t hs ht A hA
  obtain ⟨W, c, G, _, _, a, J, _, σ, hh, hgal, hspl, hsum⟩ := hA
  have hσ : ∀ j, σ j ≫ q = c ≫ p := fun j => by
    rw [← hs, ← Category.assoc, hspl.1 j]
  have ha : ∀ x, a x ≫ (c ≫ p) = c ≫ p := fun x => by
    rw [← Category.assoc, hgal.2.2.2.2.2.1 x]
  refine ⟨pullback (c ≫ p) g, bcMap g c rfl, G, inferInstance, inferInstance,
    fun x => bcMap g (a x) (ha x), J, inferInstance, fun j => bcMap g (σ j) (hσ j), ?_,
    hG g p (c ≫ p) c rfl G a ha hgal, (hS g p q (c ≫ p) s hs c rfl J σ hσ).2.2 hspl, ?_⟩
  · intro j
    rw [Category.assoc, bcMap_snd, bcMap_snd, bcMap_snd]
  · intro x
    have e : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j ≫ t) (hh j)) (bcMap_snd g _ (hh j)) x := hsum x
    have e2 : T.pull (bcMap g c rfl) (bcMap_snd g c rfl) (A x) =
        ∑ j, T.pull (bcMap g (σ j) (hσ j) ≫ bcMap g t ht)
          (by rw [Category.assoc, bcMap_snd, bcMap_snd]) x := by
      rw [e]
      exact Finset.sum_congr rfl fun j _ =>
        pull_congr T (bcMap_comp' g t (σ j) ht (hσ j) _) _ _ x
    exact pullIdentity_move T (bcMap_snd g c rfl).symm _ _ _ _ _ _ _ _ e2
end

