import Development.EtaleCohomology.EtaleSheaves.Bundle0003

-- bundled from Development.EtaleCohomology.EtaleSheaves.EtaleGroupHomologySlantOfDeltaCochain
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.E.t_D3Cut

abbrev BX (Γ : Type) [Group Γ] (X : Scheme.{0}) : Spc := cst (SingleObj Γ) ⨯ sch.obj X

def slantHom (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    (free R).obj (yoneda.obj X) ⟶ (free R).obj ((BX Γ X).obj (op (SimplexCategory.mk m))) :=
  c.sum fun g r => (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g)

def slantV (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    ((chains R).obj (sch.obj X)).X 0 ⟶ ((chains R).obj (BX Γ X)).X (-(m : ℤ)) :=
  (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (sch.obj X))).extendXIso
      ComplexShape.embeddingDownNat (i := 0) (i' := 0) (by simp)).hom ≫ slantHom R X c ≫
    (((AlgebraicTopology.alternatingFaceMapComplex (Shv R)).obj
      (((SimplicialObject.whiskering _ _).obj (free R)).obj (BX Γ X))).extendXIso
      ComplexShape.embeddingDownNat (i := m) (i' := -(m : ℤ)) (by simp)).inv

def slantCo (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ} (c : (Fin m → Γ) →₀ R) :
    Cochain ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
  Cochain.single (slantV R X c) (-(m : ℤ))

abbrev bd (R : Type) [CommRing R] {Γ : Type} [Group Γ] {m : ℕ} (b : (Fin (m + 1) → Γ) →₀ R) : (Fin m → Γ) →₀ R :=
  groupHomology.inhomogeneousChains.d (Rep.trivial R Γ R) m b

def Faces : Prop := ∀ (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (g : Fin (m + 1) → Γ),
  grpPt X g ≫ (BX Γ X).δ 0 = grpPt X (fun i => g i.succ) ∧
  ∀ j : Fin (m + 1), grpPt X g ≫ (BX Γ X).δ j.succ = grpPt X (j.contractNth (· * ·) g)

def HomD : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R),
  slantHom R X b ≫ ((chainsN R).obj (BX Γ X)).d (m + 1) m = slantHom R X (bd R b)

def DeltaCo : Prop := ∀ (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}),
  (∀ c : (Fin 0 → Γ) →₀ R, δ (-((0 : ℕ) : ℤ)) (-((0 : ℕ) : ℤ) + 1) (slantCo R X c) = 0) ∧
  ∀ (m : ℕ) (b : (Fin (m + 1) → Γ) →₀ R), δ (-((m + 1 : ℕ) : ℤ)) (-(m : ℤ)) (slantCo R X b) = slantCo R X (bd R b)

section
variable (R : Type) [CommRing R] {Γ : Type} [Group Γ] (X : Scheme.{0}) {m : ℕ}

theorem slantHom_zero : slantHom R X (0 : (Fin m → Γ) →₀ R) = 0 := Finsupp.sum_zero_index

theorem slantHom_single (g : Fin m → Γ) (r : R) :
    slantHom R X (Finsupp.single g r) = (ULift.up r : ULift.{1} R) • (free R).map (grpPt X g) :=
  Finsupp.sum_single_index (zero_smul (ULift.{1} R) _)

theorem slantHom_add (c c' : (Fin m → Γ) →₀ R) : slantHom R X (c + c') = slantHom R X c + slantHom R X c' :=
  Finsupp.sum_add_index' (fun _ => zero_smul (ULift.{1} R) _)
    (fun _ r s => add_smul (ULift.up r : ULift.{1} R) (ULift.up s) _)

theorem slantV_add (c c' : (Fin m → Γ) →₀ R) : slantV R X (c + c') = slantV R X c + slantV R X c' := by
  unfold slantV
  rw [slantHom_add]
  erw [Preadditive.add_comp, Preadditive.comp_add]

theorem slantCo_v (c : (Fin m → Γ) →₀ R) : (slantCo R X c).v 0 (-(m : ℤ)) (zero_add _) = slantV R X c :=
  Cochain.single_v _ _ _

theorem slantCo_v_ne (c : (Fin m → Γ) →₀ R) (p p' : ℤ) (h : p + -(m : ℤ) = p') (hp : p ≠ 0) :
    (slantCo R X c).v p p' h = 0 := Cochain.single_v_eq_zero _ _ _ _ _ hp

theorem slantCo_add (c c' : (Fin m → Γ) →₀ R) : slantCo R X (c + c') = slantCo R X c + slantCo R X c' := by
  ext p p' h : 1
  by_cases hp : p = 0
  · subst hp
    obtain rfl : p' = -(m : ℤ) := by omega
    rw [Cochain.add_v, slantCo_v, slantCo_v, slantCo_v, slantV_add]
  · rw [Cochain.add_v, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, slantCo_v_ne _ _ _ _ _ _ hp, add_zero]

theorem slantCo_zero : slantCo R X (0 : (Fin m → Γ) →₀ R) = 0 := by
  have h := slantCo_add R X (0 : (Fin m → Γ) →₀ R) 0
  rw [add_zero] at h
  exact left_eq_add.1 h

theorem isSlant_iff (c : (Fin m → Γ) →₀ R) (z) : IsSlant R X c z ↔ z.1 = slantCo R X c := by
  constructor
  · rintro ⟨h1, h2⟩
    ext p p' h : 1
    by_cases hp : p = 0
    · subst hp
      obtain rfl : p' = -(m : ℤ) := by omega
      rw [slantCo_v]; exact h2
    · rw [slantCo_v_ne _ _ _ _ _ _ hp]; exact h1 p p' h hp
  · intro h
    refine ⟨fun p p' hh hp => ?_, ?_⟩
    · rw [h]; exact slantCo_v_ne _ _ _ _ _ _ hp
    · rw [h]; exact slantCo_v _ _ _

end

theorem closed (h : DeltaCo) (R : Type) [CommRing R] (Γ : Type) [Group Γ] (X : Scheme.{0}) (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) :
    δ (-(m : ℤ)) (-(m : ℤ) + 1) (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m c)) = 0 := by
  cases m with
  | zero => exact (h R Γ X).1 _
  | succ m =>
    have h1 := (h R Γ X).2 m (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)
    have h2 : bd R (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c) = 0 := by
      have h3 := ConcreteCategory.congr_hom
        ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).iCycles_d (m + 1) m) c
      rw [groupHomology.inhomogeneousChains.d_def] at h3
      exact h3
    rw [h2, slantCo_zero] at h1
    have h4 : ∀ k : ℤ, k = -(m : ℤ) →
        δ (-((m + 1 : ℕ) : ℤ)) k (slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) (m + 1) c)) = 0 := by
      rintro _ rfl; exact h1
    exact h4 _ (by omega)

theorem exists_bd (R : Type) [CommRing R] (Γ : Type) [Group Γ] (m : ℕ)
    (c : groupHomology.cycles (Rep.trivial R Γ R) m) (hc : groupHomology.π (Rep.trivial R Γ R) m c = 0) :
    ∃ b, bd R b = groupHomology.iCycles (Rep.trivial R Γ R) m c := by
  have e : (ShortComplex.mk _ _ ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_comp_homologyπ (m + 1) m)).Exact :=
    ShortComplex.exact_of_g_is_cokernel _
      ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyIsCokernel (m + 1) m (by simp))
  obtain ⟨b, hb⟩ := (ShortComplex.moduleCat_exact_iff _).1 e c hc
  refine ⟨b, ?_⟩
  have h3 := ConcreteCategory.congr_hom
    ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).toCycles_i (m + 1) m) b
  rw [groupHomology.inhomogeneousChains.d_def] at h3
  rw [← hb]
  exact h3.symm

theorem cpre_add {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m : ℤ} (a a' : Cocycle K L m)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre (a + a') M n k h = cpre a M n k h + cpre a' M n k h := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  rw [AddMonoidHom.add_apply, cpre_mk, cpre_mk, cpre_mk, ← CohomologyClass.mk_add]
  congr 1
  exact Cocycle.ext (Cochain.add_comp _ _ _ h)

theorem cpre_eq_zero {C : Type*} [Category C] [Preadditive C] {K L : CochainComplex C ℤ} {m m' : ℤ} (a : Cocycle K L m)
    (hm : m' + 1 = m) (w : Cochain K L m') (hw : δ m' m w = a.1)
    (M : CochainComplex C ℤ) (n k : ℤ) (h : m + n = k) : cpre a M n k h = 0 := by
  ext x
  obtain ⟨x, rfl⟩ := x.mk_surjective
  have h1 : cpost K x m k h (CohomologyClass.mk a) = 0 := by
    rw [(CohomologyClass.mk_eq_zero_iff a).2 ⟨m', hm, w, hw⟩, map_zero]
  exact h1

theorem etale_group_homology_slant_of_delta_cochain (h : DeltaCo) : D3 := by
  intro R _ Γ _ X m
  let z : groupHomology.cycles (Rep.trivial R Γ R) m → Cocycle ((chains R).obj (sch.obj X)) ((chains R).obj (BX Γ X)) (-(m : ℤ)) :=
    fun c => Cocycle.mk _ _ rfl (closed h R Γ X m c)
  refine ⟨fun c => ⟨z c, (isSlant_iff R X _ _).2 rfl⟩, fun F n => ?_⟩
  have hex : ∃ S, IsSlantMap R Γ X F m n S := by
    let T : groupHomology.cycles (Rep.trivial R Γ R) m →+ H R (BX Γ X) F (m + n) →+ H R (sch.obj X) F n :=
      AddMonoidHom.mk' (fun c => HK.pre R (z c) F (m + n) n (by ring)) (fun c c' => by
        have : z (c + c') = z c + z c' := Cocycle.ext (by
          change slantCo R X (groupHomology.iCycles (Rep.trivial R Γ R) m (c + c')) = slantCo R X _ + slantCo R X _
          rw [map_add]; exact slantCo_add R X _ _)
        rw [this]; exact cpre_add _ _ _ _ _ _)
    have hs : Function.Surjective (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom :=
      (ModuleCat.epi_iff_surjective (groupHomology.π (Rep.trivial R Γ R) m)).1
        (inferInstanceAs (Epi ((groupHomology.inhomogeneousChains (Rep.trivial R Γ R)).homologyπ m)))
    have hk : (groupHomology.π (Rep.trivial R Γ R) m).hom.toAddMonoidHom.ker ≤ T.ker := by
      intro c hc
      obtain ⟨b, hb⟩ := exists_bd R Γ m c hc
      refine cpre_eq_zero (z c) (m' := -((m + 1 : ℕ) : ℤ)) (by omega) (slantCo R X b) ?_ _ _ _ _
      rw [(h R Γ X).2 m b, hb]; rfl
    refine ⟨AddMonoidHom.liftOfSurjective _ hs ⟨T, hk⟩, fun c z' hz' => ?_⟩
    have e : z' = z c := Cocycle.ext ((isSlant_iff R X _ _).1 hz')
    rw [e]
    exact AddMonoidHom.liftOfRightInverse_comp_apply _ _ _ ⟨T, hk⟩ c
  unfold slantR
  rw [dif_pos hex]
  exact hex.choose_spec

theorem goal_of (h : DeltaCo) : LateralTheory.E.EtaleChapterDThree :=
  fun _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ => etale_group_homology_slant_of_delta_cochain h

end LateralTheory.E.t_D3Cut
end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.H0TwistOverClosedField
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.E.E4

def Hyps : Prop :=
  A1 ∧ A2 ∧ A3 ∧ A4 ∧ A5 ∧ A7 ∧ A8 ∧ A9 ∧ A10 ∧ A11 ∧ B1 ∧ B2 ∧ B3 ∧ B4 ∧ B5 ∧ B7 ∧ C1 ∧ C2 ∧ C3 ∧ C4 ∧ C5 ∧
    D1 ∧ D2 ∧ D3 ∧ E1 ∧ E2 ∧ E3

abbrev Sp (A : Type) [CommRing A] : Scheme.{0} := Spec (CommRingCat.of A)

abbrev pl (q : ℕ) (i : ℤ) {Y X : Scheme.{0}} (f : Y ⟶ X) (m : ℤ) : Ht q (sch.obj X) m i →+ Ht q (sch.obj Y) m i :=
  pull (ZMod q) (sch.map f) (tw q i) m

def IsCurve {Ω : Type} [Field Ω] {C : Scheme.{0}} (c : C ⟶ Sp Ω) : Prop :=
  IsIntegral C ∧ IsProper c ∧ SmoothOfRelativeDimension 1 c

def SmP {Y B : Scheme.{0}} (p : Y ⟶ B) (V : B.Opens) : Prop := IsProper p ∧ Smooth (p ∣_ V)

abbrev fibMap {Y1 Y0 B S : Scheme.{0}} (g : Y1 ⟶ Y0) (p : Y0 ⟶ B) (s : S ⟶ B) : pullback (g ≫ p) s ⟶ pullback p s :=
  pullback.map (g ≫ p) s p s g (𝟙 _) (𝟙 _) (by simp) (by simp)

def H0TwistOverClosedField : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  Finite (Ht q (sp Ω) 0 i) ∧ ∀ {X : Scheme.{0}} [ConnectedSpace X] (c : X ⟶ Sp Ω), Function.Bijective (pl q i c 0)

def LeafPt : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k] [IsAlgClosed k], IsUnit (q : k) →
  ∀ {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p], topologicalKrullDim X ≤ 0 → ∀ n i : ℤ,
  Finite (Ht q (sch.obj X) n i)

def LeafComp : Prop := Hyps → ∀ (q : ℕ) (k : Type) [Field k] {X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (n i : ℤ),
  (∀ (Z : Scheme.{0}) (ι : Z ⟶ X), IsClosedImmersion ι → IsIntegral Z → Finite (Ht q (sch.obj Z) n i)) →
  ∃ (Y : Scheme.{0}) (f : Y ⟶ X), IsProper f ∧ Surjective f ∧ Finite (Ht q (sch.obj Y) n i)

def LeafDesc : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) →
  ∀ {Y X : Scheme.{0}} (p : X ⟶ Sp k) [IsProper p] (f : Y ⟶ X) [IsProper f] [Surjective f] (i : ℤ), Eqv _ (cechAug f) (tw q i)

def LeafSS : Prop := Hyps → ∀ (R : Type) [CommRing R] (F : Shv R) {Y X : Scheme.{0}} (f : Y ⟶ X) [IsProper f] (n : ℤ),
  Eqv R (cechAug f) F → (∀ (Z : Scheme.{0}) (g : Z ⟶ X), IsProper g → ∀ m < n, Finite (H R (sch.obj Z) F m)) →
  Finite (pull R (sch.map f) F n).ker

def LeafUnits : Prop := ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range)

def LeafPic : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [IsDedekindDomain B]
  [Algebra k B] [Algebra.FiniteType k B], IsUnit (q : k) → Finite {c : CommRing.Pic B // c ^ q = 1}

def LeafKum : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k B : Type) [Field k] [IsAlgClosed k] [CommRing B] [Algebra k B],
  IsUnit (q : k) → Finite (Bˣ ⧸ (powMonoidHom q : Bˣ →* Bˣ).range) → Finite {c : CommRing.Pic B // c ^ q = 1} →
  ∀ i : ℤ, Finite (Ht q (sp B) 1 i)

def LeafCurve : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) → ∀ i : ℤ,
  (∀ (B : Type) [CommRing B] [IsDedekindDomain B] [Algebra Ω B] [Algebra.FiniteType Ω B], Finite (Ht q (sp B) 1 i)) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → Finite (Ht q (sch.obj C) 1 i) ∧ Finite (Ht q (sch.obj C) 2 i) ∧
    ∀ m : ℤ, 3 ≤ m → Subsingleton (Ht q (sch.obj C) m i)

def LeafKill : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (Ω : Type) [Field Ω] [IsAlgClosed Ω], IsUnit (q : Ω) →
  ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → ∀ m i : ℤ, 0 < m → Finite (Ht q (sch.obj C) m i) →
  ∃ (C' : Scheme.{0}) (γ : C' ⟶ C), IsCurve (γ ≫ c) ∧ Surjective γ ∧ pl q i γ m = 0

def Family {k Ω : Type} [Field k] [Field Ω] (X : Scheme.{0}) {C0 C1 C2 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ1 : C1 ⟶ C0)
    (γ2 : C2 ⟶ C1) : Prop :=
  ∃ (B W Y0 Y1 Y2 : Scheme.{0}) (b : B ⟶ Sp k) (ι : W ⟶ B) (V : B.Opens) (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1)
    (h : Y0 ⟶ X) (s : Sp Ω ⟶ B) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1) (u2 : C2 ⟶ Y2),
    IsIntegral B ∧ IsProper b ∧ IsClosedImmersion ι ∧ (V : Set B) = (Set.range ι)ᶜ ∧ Set.range s ⊆ V ∧
    SmP p V ∧ SmP (g1 ≫ p) V ∧ SmP (g2 ≫ g1 ≫ p) V ∧ IsProper (g2 ≫ g1 ≫ h) ∧ Surjective (g2 ≫ g1 ≫ h) ∧
    topologicalKrullDim B < topologicalKrullDim X ∧
    topologicalKrullDim (pullback p ι : Scheme.{0}) < topologicalKrullDim X ∧
    IsPullback u0 c0 p s ∧ IsPullback u1 (γ1 ≫ c0) (g1 ≫ p) s ∧ IsPullback u2 (γ2 ≫ γ1 ≫ c0) (g2 ≫ g1 ≫ p) s ∧
    γ1 ≫ u0 = u1 ≫ g1 ∧ γ2 ≫ u1 = u2 ≫ g2

def LeafGeo : Prop := ∀ (k : Type) [Field k] [IsAlgClosed k] {X : Scheme.{0}} [IsIntegral X] (p : X ⟶ Sp k) [IsProper p],
  0 < topologicalKrullDim X → ∃ (Ω : Type) (_ : Field Ω) (_ : IsAlgClosed Ω) (_ : Algebra k Ω) (C0 : Scheme.{0})
    (c0 : C0 ⟶ Sp Ω), IsCurve c0 ∧ ∀ (C1 C2 : Scheme.{0}) (γ1 : C1 ⟶ C0) (γ2 : C2 ⟶ C1), IsCurve (γ1 ≫ c0) →
      IsCurve (γ2 ≫ γ1 ≫ c0) → Surjective γ1 → Surjective γ2 → Family (k := k) X c0 γ1 γ2

def LeafSpec : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B Y0 Y1 : Scheme.{0}} [IsIntegral B] (_ : B ⟶ Sp k) (V : B.Opens) (p : Y0 ⟶ B) (g : Y1 ⟶ Y0), SmP p V → SmP (g ≫ p) V →
  ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] (s : Sp Ω ⟶ B), Set.range s ⊆ V →
  ∀ {C0 C1 : Scheme.{0}} (c0 : C0 ⟶ Sp Ω) (γ : C1 ⟶ C0) (u0 : C0 ⟶ Y0) (u1 : C1 ⟶ Y1),
    IsPullback u0 c0 p s → IsPullback u1 (γ ≫ c0) (g ≫ p) s → γ ≫ u0 = u1 ≫ g →
  ∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, Subsingleton (Ht q (sch.obj C0) m i) → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧
    (∀ m, pl q i γ m = 0 → pl q i (fibMap g p t) m = 0) ∧
    (Function.Bijective (pl q i (γ ≫ c0) 0) → Function.Bijective (pl q i (pullback.snd (g ≫ p) t) 0))

def LeafGhost : Prop := Hyps → ∀ (q : ℕ) [NeZero q] (k : Type) [Field k], IsUnit (q : k) → ∀ (i : ℤ)
  {B W Y0 Y1 Y2 : Scheme.{0}} (_ : B ⟶ Sp k) (ι : W ⟶ B) [IsClosedImmersion ι] (V : B.Opens), (V : Set B) = (Set.range ι)ᶜ →
  ∀ (p : Y0 ⟶ B) (g1 : Y1 ⟶ Y0) (g2 : Y2 ⟶ Y1), IsProper p → IsProper (g1 ≫ p) → IsProper (g2 ≫ g1 ≫ p) →
  (∀ (A : Type) [CommRing A] (t : Sp A ⟶ B), SH A → Set.range t ⊆ V →
    (∀ m, 3 ≤ m → Subsingleton (Ht q (sch.obj (pullback p t)) m i)) ∧ pl q i (fibMap g1 p t) 2 = 0 ∧
    pl q i (fibMap g2 (g1 ≫ p) t) 1 = 0 ∧ Function.Bijective (pl q i (pullback.snd (g2 ≫ g1 ≫ p) t) 0)) →
  ∀ (n : ℤ) (a : Ht q (sch.obj Y0) n i), pl q i (pullback.fst p ι) n a = 0 →
    ∃ b : Ht q (sch.obj B) n i, pl q i (g2 ≫ g1 ≫ p) n b = pl q i (g2 ≫ g1) n a

theorem fin_of {A C D E : Type*} [AddCommGroup A] [AddCommGroup C] [AddCommGroup D] [AddCommGroup E] (φ : A →+ C)
    (r : A →+ D) (ψ : E →+ C) [Finite D] [Finite E] (hk : Finite φ.ker) (h : ∀ a, r a = 0 → ∃ b, ψ b = φ a) : Finite A := by
  rw [AddMonoidHom.finite_iff_finite_ker_range r]
  refine ⟨?_, inferInstance⟩
  rw [AddMonoidHom.finite_iff_finite_ker_range (φ.comp r.ker.subtype)]
  constructor
  · exact Finite.of_injective (fun x : (φ.comp r.ker.subtype).ker => (⟨x.1.1, x.2⟩ : φ.ker))
      (fun x y hxy => Subtype.ext (Subtype.ext (congrArg (fun z : φ.ker => z.1) hxy)))
  · have : (Set.range ψ).Finite := Set.finite_range _
    refine Set.Finite.subset this ?_
    rintro _ ⟨a, rfl⟩
    exact h a.1 a.2

theorem pl_comp (q : ℕ) (i : ℤ) {Z Y X : Scheme.{0}} (g : Z ⟶ Y) (f : Y ⟶ X) (m : ℤ) (x : Ht q (sch.obj X) m i) :
    pl q i (g ≫ f) m x = pl q i g m (pl q i f m x) := by
  rw [← pull_comp, ← Functor.map_comp]

theorem goal_of (hH0 : H0TwistOverClosedField) (hPt : LeafPt) (hComp : LeafComp) (hDesc : LeafDesc) (hSS : LeafSS) (hU : LeafUnits)
    (hPic : LeafPic) (hKum : LeafKum) (hCurve : LeafCurve) (hKill : LeafKill) (hGeo : LeafGeo) (hSpec : LeafSpec)
    (hGhost : LeafGhost) : LateralTheory.E.EtaleChapterEFour := by
  intro a1 a2 a3 a4 a5 a7 a8 a9 a10 a11 b1 b2 b3 b4 b5 b7 c1 c2 c3 c4 c5 d1 d2 d3 e1 e2 e3
  have hy : Hyps := ⟨a1, a2, a3, a4, a5, a7, a8, a9, a10, a11, b1, b2, b3, b4, b5, b7, c1, c2, c3, c4, c5, d1, d2, d3, e1, e2, e3⟩
  intro q _ k _ _ hq X p _ n i
  have step : ∀ n : ℤ, (∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < n, Finite (Ht q (sch.obj X) m i)) →
      ∀ (e : WithBot ℕ∞) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
    intro n Q
    have ker : ∀ (X Y : Scheme.{0}) (p : X ⟶ Sp k) (f : Y ⟶ X), IsProper p → IsProper f → Surjective f →
        Finite (pl q i f n).ker := fun X Y p f _ _ _ =>
      hSS hy _ _ f n (hDesc hy q k hq p f i) (fun Z g _ => Q Z (g ≫ p) inferInstance)
    intro e
    induction e using WellFoundedLT.induction with
    | ind e IH =>
    have int : ∀ (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → IsIntegral X → topologicalKrullDim X ≤ e →
        Finite (Ht q (sch.obj X) n i) := by
      intro X p _ _ he
      rcases le_or_gt (topologicalKrullDim X) 0 with h0 | h0
      · exact hPt hy q k hq p h0 n i
      obtain ⟨Ω, _, _, _, C0, c0, hc0, hall⟩ := hGeo k p h0
      have hΩ : IsUnit (q : Ω) := by simpa using hq.map (algebraMap k Ω)
      have hc : ∀ {C : Scheme.{0}} (c : C ⟶ Sp Ω), IsCurve c → _ := fun c => hCurve hy q Ω hΩ i
        (fun B _ _ _ _ => hKum hy q Ω B hΩ (hU q Ω B) (hPic hy q Ω B hΩ) i) c
      obtain ⟨C1, γ1, hc1, s1, z1⟩ := hKill hy q Ω hΩ c0 hc0 2 i (by norm_num) (hc c0 hc0).2.1
      obtain ⟨C2, γ2, hc2, s2, z2⟩ := hKill hy q Ω hΩ (γ1 ≫ c0) hc1 1 i (by norm_num) (hc _ hc1).1
      obtain ⟨B, W, Y0, Y1, Y2, b, ι, V, π, g1, g2, h, s, u0, u1, u2, _, _, _, hV, hs, m0, m1, m2, f1, f2, dB, dW,
        P0, P1, P2, w1, w2⟩ := hall C1 C2 γ1 γ2 hc1 hc2 s1 s2
      have := m0.1
      have := hc2.1
      have fB := IH _ (dB.trans_le he) B b inferInstance le_rfl
      have fW := IH _ (dW.trans_le he) (pullback π ι) (pullback.fst π ι ≫ π ≫ b) inferInstance le_rfl
      have G := hGhost hy q k hq i b ι V hV π g1 g2 m0.1 m1.1 m2.1 (fun A _ t hA ht => by
        have S1 := hSpec hy q k hq i b V π g1 m0 m1 Ω s hs c0 γ1 u0 u1 P0 P1 w1 A t hA ht
        have S2 := hSpec hy q k hq i b V (g1 ≫ π) g2 m1 m2 Ω s hs (γ1 ≫ c0) γ2 u1 u2 P1 P2 w2 A t hA ht
        exact ⟨fun m hm => S1.1 m ((hc c0 hc0).2.2 m hm), S1.2.1 2 z1, S2.2.1 1 z2,
          S2.2.2 ((hH0 hy q Ω hΩ i).2 _)⟩) n
      refine fin_of (pl q i (g2 ≫ g1 ≫ h) n) (pl q i (pullback.fst π ι ≫ h) n) (pl q i (g2 ≫ g1 ≫ π) n)
        (ker X Y2 p _ inferInstance f1 f2) (fun a ha => ?_)
      rw [pl_comp] at ha
      obtain ⟨x, hx⟩ := G _ ha
      exact ⟨x, by rw [hx, ← pl_comp, Category.assoc]⟩
    intro X p _ he
    obtain ⟨Y, f, f1, f2, f3⟩ := hComp hy q k p n i (fun Z ι _ _ =>
      int Z (ι ≫ p) inferInstance inferInstance (ι.isClosedEmbedding.isInducing.topologicalKrullDim_le.trans he))
    have := ker X Y p f inferInstance f1 f2
    rw [AddMonoidHom.finite_iff_finite_ker_range (pl q i f n)]
    exact ⟨this, inferInstance⟩
  have all : ∀ (N : ℕ) (X : Scheme.{0}) (p : X ⟶ Sp k), IsProper p → ∀ m < (N : ℤ), Finite (Ht q (sch.obj X) m i) := by
    intro N
    induction N with
    | zero =>
      intro X p _ m hm
      have := (a9 (ZMod q) (tw q i)).1 (sch.obj X) m (by simpa using hm)
      exact Finite.of_subsingleton
    | succ N IH =>
      intro X p hp m hm
      rcases lt_or_eq_of_le (show m ≤ N by omega) with h | h
      · exact IH X p hp m h
      · subst h
        exact step _ IH _ X p hp le_rfl
  exact all (n.toNat + 1) X p inferInstance n (by omega)

end LateralTheory.E.E4

end
end

-- bundled from Development.EtaleCohomology.EtaleSheaves.LeafChartRing
section
noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex GlobalTheory.EtC

namespace LateralTheory.E.t_E6Cut

def ConnK (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L) : Prop :=
  ∀ n : ℤ, (n < c - 1 → Function.Bijective (HK.pull R f F n)) ∧ (n < c → Function.Injective (HK.pull R f F n))

def Conn (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E') : Prop := ConnK R F c ((chains R).map f)

def EtLoc (T : Scheme.{0}) (P : ∀ V : Scheme.{0}, (V ⟶ T) → Prop) : Prop :=
  ∃ S ∈ Scheme.etaleTopology.{0} T, ∀ (V : Scheme.{0}) (k : V ⟶ T), S k → P V k

def sxMap {E E' : Spc} (f : E ⟶ E') {p : ℕ} {T : Scheme.{0}} (x : Sx E p T) : Sx E' p T :=
  (f.app (op (SimplexCategory.mk p))).app (op T) x

def sxRes {E : Spc} {p : ℕ} {V T : Scheme.{0}} (k : V ⟶ T) (x : Sx E p T) : Sx E p V :=
  (E.obj (op (SimplexCategory.mk p))).map k.op x

def QIso {B W : Type} [CommRing B] [CommRing W] (α : B →+* W) (I : Ideal B) : Prop :=
  Function.Bijective (Ideal.quotientMap (I.map α) α Ideal.le_comap_map)

def varIdeal {d : ℕ} {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B) : Ideal B :=
  Ideal.span (Set.range fun j => φ (MvPolynomial.X j))

def IsCompl' {B : Type} [CommRing B] (I : Ideal B) (U : (Spec (CommRingCat.of B)).Opens) : Prop :=
  ∀ x : Spec (CommRingCat.of B), x ∈ U ↔ ¬ I ≤ (show PrimeSpectrum B from x).asIdeal

def LeafRel : Prop := ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {K L : Cx R} (f : K ⟶ L),
  ConnK R F c f ↔ ∀ n < c, Subsingleton (HK R (mappingCone f) F n)

def LeafLevel : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {E E' : Spc} (f : E ⟶ E'),
  (∀ p : ℕ, Conn R F (c - p) (disc.map (f.app (op (SimplexCategory.mk p))))) → Conn R F c f

def LeafProd : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) {Y : Scheme.{0}} {ι : Type} (V : ι → Scheme.{0})
  (j : ∀ a, V a ⟶ Y) [∀ a, IsOpenImmersion (j a)], (∀ a b, a ≠ b → Disjoint (Set.range (j a)) (Set.range (j b))) →
  (∀ y : Y, ∃ a, y ∈ Set.range (j a)) → ∀ n : ℤ,
  Function.Bijective fun (x : H R (sch.obj Y) F n) (a : ι) => pull R (sch.map (j a)) F n x

def LeafLoc : Prop := A1 → A2 → A9 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {X : Scheme.{0}} (U : X.Opens),
  (∀ x : X, x ∉ U → ∀ W : X.Opens, x ∈ W → ∃ (Y : Scheme.{0}) (j : Y ⟶ X) (_ : IsOpenImmersion j),
    x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧ Conn R F c (sch.map (j ⁻¹ᵁ U).ι)) →
  Conn R F c (sch.map U.ι)

def LeafExc : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {U E' E : Spc} (f : U ⟶ E) [Mono f] (g : E' ⟶ E),
  (∀ (p : ℕ) (T : Scheme.{0}) (y : Sx E p T), EtLoc T fun V k =>
    (∃ u : Sx U p V, sxMap f u = sxRes k y) ∨ ∃ a : Sx E' p V, sxMap g a = sxRes k y) →
  (∀ (p : ℕ) (T : Scheme.{0}) (a b : Sx E' p T), sxMap g a = sxMap g b → EtLoc T fun V k =>
    sxRes k a = sxRes k b ∨ ∃ u : Sx U p V, sxMap f u = sxRes k (sxMap g a)) →
  (Conn R F c f ↔ Conn R F c (pullback.snd f g))

def LeafExcRing : Prop := A1 → ∀ (R : Type) [CommRing R] (F : Shv R) (c : ℤ) {B W : Type} [CommRing B] [CommRing W]
  (α : B →+* W) (I : Ideal B), α.Etale → QIso α I → ∀ (U : (Spec (CommRingCat.of B)).Opens)
  (U' : (Spec (CommRingCat.of W)).Opens), IsCompl' I U → IsCompl' (I.map α) U' →
  (Conn R F c (sch.map U.ι) ↔ Conn R F c (sch.map U'.ι))

def LeafRoof : Prop := ∀ (d : ℕ) {C B : Type} [CommRing C] [CommRing B] (φ : MvPolynomial (Fin d) C →+* B), φ.Etale →
  ∃ (D W : Type) (_ : CommRing D) (_ : CommRing W) (_ : B →+* D) (α : B →+* W) (β : MvPolynomial (Fin d) D →+* W),
    α.Etale ∧ β.Etale ∧ (∀ j, α (φ (MvPolynomial.X j)) = β (MvPolynomial.X j)) ∧ QIso α (varIdeal φ) ∧
    QIso β (varIdeal (RingHom.id (MvPolynomial (Fin d) D)))

def LeafChartRing : Prop := ∀ (d e : ℕ) (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (I : Ideal B),
  Algebra.IsStandardSmoothOfRelativeDimension (e + d) A B → Algebra.IsStandardSmoothOfRelativeDimension e A (B ⧸ I) →
  ∀ P : Ideal B, P.IsPrime → I ≤ P → ∃ g ∉ P, ∃ (C : Type) (_ : CommRing C)
    (φ : MvPolynomial (Fin d) C →+* Localization.Away g), φ.Etale ∧ I.map (algebraMap B _) = varIdeal φ

def LeafChart : Prop := ∀ {X Z S : Scheme.{0}} (p : X ⟶ S) (ι : Z ⟶ X) [IsClosedImmersion ι] (d e : ℕ)
  [SmoothOfRelativeDimension (e + d) p] [SmoothOfRelativeDimension e (ι ≫ p)] (x : X), x ∈ Set.range ι →
  ∀ W : X.Opens, x ∈ W → ∃ (B C : Type) (_ : CommRing B) (_ : CommRing C) (j : Spec (CommRingCat.of B) ⟶ X)
    (_ : IsOpenImmersion j) (φ : MvPolynomial (Fin d) C →+* B), φ.Etale ∧ x ∈ Set.range j ∧ Set.range j ⊆ (W : Set X) ∧
    ∀ y : Spec (CommRingCat.of B), j y ∈ Set.range ι ↔ varIdeal φ ≤ (show PrimeSpectrum B from y).asIdeal

def LeafNat : Prop := A1 → A5 → A7 → A9 → A10 → DivisorNaturality

def LeafProj : Prop := A1 → A5 → A7 → A9 → A10 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) {E : Spc} {N : ℕ}
  (V : E ⟶ ofCat (glCat N)) (V' : E ⟶ ofCat (glCat (N + 1))), Inv q E →
  ∀ s : pullback V (PGL.pr N) ⟶ pullback V' (PGL.pr (N + 1)), s ≫ pullback.fst _ _ = pullback.fst _ _ →
    s ≫ pullback.snd _ _ ≫ PGL.line (N + 1) = pullback.snd _ _ ≫ PGL.line N → Conn _ (tw q i) (2 * N) s

def LeafHI : Prop := B3 → C4 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (X : Scheme.{0}), IsUnit (q : Γ(X, ⊤)) →
  Eqv _ (sch.map (𝔸(Fin 1; X) ↘ X)) (tw q i)

def LeafAff : Prop := A1 → A3 → A5 → A7 → A9 → A10 → B3 → C4 → D1 → ∀ (q : ℕ) [NeZero q] (i : ℤ) (d : ℕ) (D : Type)
  [CommRing D], IsUnit (q : D) → ∀ U : (Spec (CommRingCat.of (MvPolynomial (Fin d) D))).Opens,
  IsCompl' (varIdeal (RingHom.id (MvPolynomial (Fin d) D))) U → Conn _ (tw q i) (2 * d) (sch.map U.ι)

theorem exists_compl {B : Type} [CommRing B] (I : Ideal B) : ∃ U, IsCompl' I U :=
  ⟨⟨(PrimeSpectrum.zeroLocus (I : Set B))ᶜ, (PrimeSpectrum.isClosed_zeroLocus _).isOpen_compl⟩, fun _ => Iff.rfl⟩

theorem map_varIdeal {d : ℕ} {C B W : Type} [CommRing C] [CommRing B] [CommRing W] (φ : MvPolynomial (Fin d) C →+* B)
    (α : B →+* W) : (varIdeal φ).map α = Ideal.span (Set.range fun j => α (φ (MvPolynomial.X j))) := by
  rw [varIdeal, Ideal.map_span, ← Set.range_comp]; rfl

theorem goal_of (hLoc : LeafLoc) (hExc : LeafExcRing) (hRoof : LeafRoof) (hChart : LeafChart) (hAff : LeafAff) :
    LateralTheory.E.EtaleChapterESix := by
  intro a1 a2 a3 _ a5 a7 _ a9 a10 _ _ _ b3 _ _ _ _ _ _ c4 _ d1 _ _ _ _ _ _ q _ X Z S p ι _ d e _ _ hq U hU n i
  refine hLoc a1 a2 a9 _ (tw q i) (2 * d) U (fun x hx W hW => ?_) n
  have hmem : ∀ y : X, y ∈ U ↔ y ∉ Set.range ι := fun y => by
    change y ∈ (U : Set X) ↔ _
    rw [hU]; rfl
  obtain ⟨B, C, _, _, j, hj, φ, hφ, hxj, hjW, hz⟩ := hChart p ι d e x (by by_contra h; exact hx ((hmem x).2 h)) W hW
  refine ⟨_, j, hj, hxj, hjW, ?_⟩
  obtain ⟨D, W', _, _, ψ, α, β, hα, hβ, hc, qα, qβ⟩ := hRoof d φ hφ
  have hqB : IsUnit (q : B) := by
    simpa using hq.map ((j ≫ p).appTop ≫ (Scheme.ΓSpecIso (CommRingCat.of B)).hom).hom
  have hqD : IsUnit (q : D) := by simpa using hqB.map ψ
  obtain ⟨U', hU'⟩ := exists_compl ((varIdeal φ).map α)
  obtain ⟨U₀, hU₀⟩ := exists_compl (varIdeal (RingHom.id (MvPolynomial (Fin d) D)))
  have he : (varIdeal (RingHom.id (MvPolynomial (Fin d) D))).map β = (varIdeal φ).map α := by
    rw [map_varIdeal, map_varIdeal]
    simp only [hc, RingHom.id_apply]
  have h1 := (hExc a1 _ (tw q i) (2 * d) β _ hβ qβ U₀ U' hU₀ (he ▸ hU')).1
    (hAff a1 a3 a5 a7 a9 a10 b3 c4 d1 q i d D hqD U₀ hU₀)
  refine (hExc a1 _ (tw q i) (2 * d) α _ hα qα _ U' (fun y => ?_) hU').2 h1
  exact (hmem (j y)).trans (not_congr (hz y))

end LateralTheory.E.t_E6Cut
end
end

