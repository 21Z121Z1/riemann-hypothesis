import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0015
import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.TwGood

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.MixedPositionHypothesis
section
noncomputable section

namespace Formalism.MainNotions.N.Ln34

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Module Formalism.MainNotions.ElementDenominator Formalism.MainNotions.ElementDenominator.CongruenceModules

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (K LL : FinExt l)

def quotA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L),
    IsCrys (P.PD K) T₁.ρ → IsCrys (P.PD K) T₂.ρ → F.Onto →
    ∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X

def normA : Prop :=
  ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (r S η m h : ℕ)
    (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
    HypA P K LL T₁ T₂ F r S η m h up b →
    (∀ τ (X : Set ℤ), JumpsInV (P.PD K) T₁.ρ τ X → JumpsInV (P.PD K) T₂.ρ τ X) →
    ∃ (η₁ h' : ℕ) (b' : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ), η₁ ≤ η ∧ h' ≤ h + S + 1 ∧
      HypN P K LL T₁ T₂ F S η₁ m h' up b'

end Local

def quotR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → quotA (D.loc l) K LL

def normR (D : D7) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → normA (D.loc l) K LL

def dvdR : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ K LL : FinExt l, Good K 1 LL → eK K ∣ l - 1

def p9R (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)), IsCrys ((D.loc l).PD K) T.ρ →
    ∃ (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
      (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
      Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E

def splitR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (h' : ℕ), 1 ≤ h' → IsCrys ((D.loc l).PD K) T.ρ →
    (∀ τ, JumpsInV ((D.loc l).PD K) T.ρ τ (Set.Icc (-(h' : ℤ)) h')) →
    ∀ κ ∈ latticeFiniteCocycles ((D.loc l).PD K) T.L,
      (l ^ (rhoA l (eK K) h' + sigA l (sK l K) h') : ℕ) • κ ∈
        (⨆ c, JZ ((HW l).W K 1 LL hG) T π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c) ⊔ latticeCoboundaries T.L

def univR (D : D7) (HW : HWOf D.loc) : Prop :=
  ∀ (l : ℕ) [Fact l.Prime], l ≠ 2 → ∀ (K LL : FinExt l) (hG : Good K 1 LL)
    (π' : LetA ↥(OL LL) (finrank ℚ_[l] ↥(K0 K)))
    (E : ZMod (finrank ℚ_[l] ↥(K0 K)) → Polynomial ↥(OL LL)),
    Formalism.MainNotions.DeltaInvariantLattices.wachRingRelations ((HW l).W K 1 LL hG) (eK K) (sK l K) π' E →
    ∀ (T₁ T₂ : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (F : LatHom T₁.L T₂.L) (S η m h' : ℕ)
      (up : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → Bool) (b : (↥K.1 →ₐ[ℚ_[l]] ↥LL.1) → ℕ),
      HypN (D.loc l) K LL T₁ T₂ F S η m h' up b →
      ∀ c : ZMod (finrank ℚ_[l] ↥(K0 K)), ∃ s₀ : Finset (↥(GK K) → T₂.V),
        s₀.card ≤ eK K * (eK K + 1) * m ∧
        (s₀ : Set (↥(GK K) → T₂.V)) ⊆ latticeFiniteCocycles ((D.loc l).PD K) T₂.L ∧
        ∀ x ∈ JZ ((HW l).W K 1 LL hG) T₂ π' (Formalism.MainNotions.DeltaInvariantLattices.Eat E π') h' (MK l K h') c,
          (l ^ (sigA l (sK l K) h' + y2K l K h' S η) : ℕ) • x ∈
            F.ImF ((D.loc l).PD K) ⊔ Submodule.span ↥(OL LL) (s₀ : Set (↥(GK K) → T₂.V))

theorem YA_split (l e s h' S η : ℕ) :
    YA l e s h' S η = (rhoA l e h' + sigA l s h') + (sigA l s h' +
      (2 * sigA l s h' + kapA l e h' S + rhoA l e h' + max (2 * sigA l s h') (ycA l h' η))) := by
  unfold YA
  ring

theorem YA_mono (l e s h' S : ℕ) {η₁ η : ℕ} (h : η₁ ≤ η) : YA l e s h' S η₁ ≤ YA l e s h' S η := by
  rw [YA_split, YA_split]
  unfold ycA
  gcongr

theorem annihilation_of_scaled_spans {O M ι : Type} [CommRing O] [AddCommGroup M] [Module O M] [Fintype ι] [DecidableEq M]
    (J : ι → Submodule O M) (B Im : Submodule O M) (s : ι → Finset M) (hB : B ≤ Im) (a b : ℕ) (p : M)
    (hp : a • p ∈ (⨆ c, J c) ⊔ B) (hU : ∀ c, ∀ x ∈ J c, b • x ∈ Im ⊔ Submodule.span O (s c : Set M)) :
    b • a • p ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
  classical
  have key : (⨆ c, J c) ≤
      (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im).comap
        (b • LinearMap.id : M →ₗ[O] M) := by
    refine iSup_le fun c y hy => ?_
    have h1 := hU c y hy
    have hle : Im ⊔ Submodule.span O (s c : Set M) ≤
        Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := by
      refine sup_le le_sup_right (le_sup_of_le_left (Submodule.span_mono ?_))
      intro z hz
      exact Finset.mem_coe.2 (Finset.mem_biUnion.2 ⟨c, Finset.mem_univ _, Finset.mem_coe.1 hz⟩)
    show b • y ∈ (Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im)
    exact hle h1
  obtain ⟨x, hx, y, hy, hxy⟩ := Submodule.mem_sup.1 hp
  rw [← hxy, smul_add]
  have hx' : b • x ∈ Submodule.span O ((Finset.univ.biUnion s : Finset M) : Set M) ⊔ Im := key hx
  exact Submodule.add_mem _ hx' (Submodule.mem_sup_right (nsmul_mem (hB hy) b))

set_option maxHeartbeats 2000000 in

theorem killR_of_steps (D : D7) (HW : HWOf D.loc) (hd : dvdR) (hq : quotR D) (hn : normR D)
    (h9 : p9R D HW) (hS : splitR D HW) (hU : univR D HW) : killR D := by
  classical
  unfold killR
  intro l _ hl K LL hG
  unfold killA
  intro T₁ T₂ F r S η m h up b hA
  have hjmp : ∀ τ (X : Set ℤ), JumpsInV ((D.loc l).PD K) T₁.ρ τ X → JumpsInV ((D.loc l).PD K) T₂.ρ τ X :=
    hq l hl K LL hG T₁ T₂ F hA.1 hA.2.1 hA.2.2.1
  obtain ⟨η₁, h', b', hη, hh', hN⟩ := hn l hl K LL hG T₁ T₂ F r S η m h up b hA hjmp
  have hc2 := hN.2.1
  have hj2 := hN.2.2.2.2.1
  have hηb := hN.2.2.2.2.2.1
  have hbS := hN.2.2.2.2.2.2.1
  have hh1 := hN.2.2.2.2.2.2.2.1
  obtain ⟨π', E, h9'⟩ := h9 l hl K LL hG T₂ hc2
  have hjmp2 : ∀ τ, JumpsInV ((D.loc l).PD K) T₂.ρ τ (Set.Icc (-(h' : ℤ)) h') := by
    intro τ a ha
    have hmem := hj2 τ a ha
    have h1 := hηb τ
    have h2 := hbS τ
    rcases hmem with hmem | hmem
    · unfold deep at hmem
      split_ifs at hmem
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
      · obtain ⟨x1, x2⟩ := hmem
        constructor <;> omega
    · obtain ⟨x1, x2⟩ := hmem
      constructor <;> omega
  have hSp := hS l hl K LL hG π' E h9' T₂ h' hh1 hc2 hjmp2
  choose s₀ hs₀card hs₀sub hs₀J using fun c => hU l hl K LL hG π' E h9' T₁ T₂ F S η₁ m h' up b' hN c
  have hB : latticeCoboundaries T₂.L ≤ F.ImF ((D.loc l).PD K) := by
    unfold LatHom.ImF
    exact le_sup_right
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := K.2
  haveI : NeZero (finrank ℚ_[l] ↥(K0 K)) := by
    first
    | infer_instance
    | exact ⟨Module.finrank_pos.ne'⟩
    | exact ⟨(Formalism.MainNotions.N.Ln34.max_unramified_finrank_pos K).ne'⟩
    | exact ⟨(Formalism.MainNotions.N.PreambleDegrees.finrank_maxUnramifiedSubfield_padicFinExt_pos K).ne'⟩
    | (haveI := Formalism.MainNotions.WachCoordinates.Br.finiteDimensional_max_unramified K; exact ⟨Module.finrank_pos.ne'⟩)
    | (haveI := FiniteDimensional.left ℚ_[l] ↥(K0 K) ↥K.1; exact ⟨Module.finrank_pos.ne'⟩)
  refine ⟨sK l K, h', Nat.mul_div_cancel' (hd l hl K LL hG), hh1, hh', Finset.univ.biUnion s₀, ?_, ?_, ?_⟩
  · calc (Finset.univ.biUnion s₀).card ≤ ∑ c, (s₀ c).card := Finset.card_biUnion_le
      _ ≤ ∑ _c : ZMod (finrank ℚ_[l] ↥(K0 K)), eK K * (eK K + 1) * m :=
        Finset.sum_le_sum fun c _ => hs₀card c
      _ = _ := by
        rw [Finset.sum_const, Finset.card_univ, ZMod.card, smul_eq_mul]
        ring
  · intro x hx
    obtain ⟨c, -, hc⟩ := Finset.mem_biUnion.1 (Finset.mem_coe.1 hx)
    exact hs₀sub c hc
  · intro p hp
    have hk := annihilation_of_scaled_spans _ _ _ s₀ hB _ _ p (hSp p hp) (fun c x hx => hs₀J c x hx)
    have hY : (l ^ YA l (eK K) (sK l K) h' S η₁ : ℕ) • p ∈
        Submodule.span ↥(OL LL) ((Finset.univ.biUnion s₀ : Finset _) : Set (↥(GK K) → T₂.V)) ⊔
          F.ImF ((D.loc l).PD K) := by
      rw [YA_split, pow_add, mul_comm, mul_smul]
      exact hk
    have e1 : YA l (eK K) (sK l K) h' S η =
        (YA l (eK K) (sK l K) h' S η - YA l (eK K) (sK l K) h' S η₁) + YA l (eK K) (sK l K) h' S η₁ :=
      (Nat.sub_add_cancel (YA_mono l (eK K) (sK l K) h' S hη)).symm
    rw [e1, pow_add, mul_smul]
    exact nsmul_mem hY _

end Formalism.MainNotions.N.Ln34

end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.SemisimpleLetterIffForallMem
section
noncomputable section

namespace Formalism.MainNotions.UnusedSlot35.DssRec

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc

theorem rec_exists {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    (F : ℕ → M → M) (y₀ : M) : ∃ s : ℕ → M, s 0 = y₀ ∧ ∀ k, p • s (k + 1) = F k (s k) := by
  obtain ⟨u, hu⟩ := hp
  let s : ℕ → M := fun k => Nat.rec y₀ (fun k sk => ((u⁻¹ : Eˣ) : E) • F k sk) k
  refine ⟨s, rfl, fun k => ?_⟩
  show p • (((u⁻¹ : Eˣ) : E) • F k (s k)) = F k (s k)
  rw [← algebraMap_smul E p, ← hu, smul_smul, Units.mul_inv, one_smul]

theorem smul_inj {R E M : Type} [CommRing R] [CommRing E] [Algebra R E] [AddCommGroup M]
    [Module R M] [Module E M] [IsScalarTower R E M] (p : R) (hp : IsUnit (algebraMap R E p))
    {a b : M} (h : p • a = p • b) : a = b := by
  obtain ⟨u, hu⟩ := hp
  have h' : (u : E) • a = (u : E) • b := by
    rw [hu, algebraMap_smul, algebraMap_smul]
    exact h
  have := congrArg (fun m => ((u⁻¹ : Eˣ) : E) • m) h'
  simpa [smul_smul] using this

theorem rec_unique {R E O M : Type} [CommRing R] [CommRing E] [CommRing O] [Algebra R E]
    [AddCommGroup M] [Module R M] [Module E M] [Module O M] [IsScalarTower R E M] (p : R)
    (hp : IsUnit (algebraMap R E p)) (c : ℕ → O) (Gm : M → M) (L : ℕ) (s s' : ℕ → M)
    (h0 : s 0 = s' 0)
    (hs : ∀ k, k < L → p • (s (k + 1) + c k • s k) = Gm (s k))
    (hs' : ∀ k, k < L → p • (s' (k + 1) + c k • s' k) = Gm (s' k)) :
    ∀ k, k ≤ L → s k = s' k := by
  intro k hk
  induction k with
  | zero => exact h0
  | succ k ih =>
    have ih' := ih (by omega)
    have h1 := hs k (by omega)
    have h2 := hs' k (by omega)
    rw [← ih'] at h2
    have := smul_inj (E := E) p hp (h1.trans h2.symm)
    exact add_right_cancel this

section Core

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {PD : PeriodData G Qp K₀ K B BdR} {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL]
    [CommRing O] [Algebra O LL] {v : AddValuation LL (WithTop ℚ)} {n : ℕ}

theorem π₀_unit (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) (hA : Formalism.MainNotions.LiftingTheory.CaseA W)
    (T : LocLat G Qp LL O) (hT : IsCrys PD T.ρ) : IsUnit (algebraMap (LetA O n) W.EE W.π₀) := by
  have hK : Module.finrank K₀ K = 1 := by
    rw [← (LinearEquiv.ofBijective (Algebra.linearMap K₀ K) hA.1).finrank_eq, Module.finrank_self]
  obtain ⟨w, hw⟩ := ((h9 T hT hA.2.1 hA.2.2).2.2 hK).1.2.2.1
  rw [hw, map_mul, map_pow]
  exact (w.isUnit.map _).mul (W.EE_π.pow _)

def DssMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (Y : ℕ) (y₀ : W.DD T), Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.N T → (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi)
            (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • seq k) = W.γD T W.gam (seq k) - seq k) →
        seq (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length ∈ W.N T

theorem coreDss_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.LiftingTheory.coreDss W ↔ DssMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.LiftingTheory.xList W T (Formalism.MainNotions.LiftingTheory.Mmax n Mi) (Formalism.MainNotions.LiftingTheory.Mmax n hi) Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO Y y₀ hY hδ s hs0 hrec⟩

def DssLetMem (W : LocWach PD LL O v n) : Prop :=
  Formalism.MainNotions.LiftingTheory.CaseA W → ∀ (T : LocLat G Qp LL O) (Mi hi : ZMod n → ℕ), IsCrys PD T.ρ →
    Formalism.MainNotions.LiftingTheory.JumpsLet W T Mi hi →
    ∀ (ug : Oˣ), ug ^ (PD.p - 1) = (W.χΓ W.gam) ^ (PD.p - 1) →
      v (algebraMap O LL ((ug : O) - 1)) = 1 →
    ∀ cO : ℤ → O, (∀ x : ℤ, ((PD.p : ℕ) : O) * cO x = 1 - ((ug ^ (-x) : Oˣ) : O)) →
    ∀ (i : ZMod n) (y' Y : ℕ) (y₀ : W.DD T), y' ≤ Y → Formalism.MainNotions.LiftingTheory.qp W ^ Y • y₀ ∈ W.Nl T i →
      (∀ δ ∈ W.DelF, W.γD T δ y₀ = y₀) →
      ∀ seq : ℕ → W.DD T, seq 0 = y₀ →
        (∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
          W.π₀ • (seq (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • seq k) =
            W.γD T W.gam (seq k) - seq k) →
        Formalism.MainNotions.LiftingTheory.qp W ^ y' • seq (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length ∈ W.Nl T i

theorem dssLet_iff_mem (W : LocWach PD LL O v n) (h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W W) :
    Formalism.MainNotions.RamifiedCoefficientChains.DssLet W ↔ DssLetMem W := by
  constructor
  · intro hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ seq h0 hrec
    obtain ⟨s, hs0, hsrec, hsN⟩ := hc hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    have heq := rec_unique (E := W.EE) W.π₀ hu
      (fun k => cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0))
      (fun m => W.γD T W.gam m - m) _ s seq (hs0.trans h0.symm) hsrec hrec _ le_rfl
    rw [← heq]
    exact hsN
  · intro hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ
    have hu := π₀_unit W h9 hA T hT
    obtain ⟨s, hs0, hs⟩ := rec_exists (E := W.EE) W.π₀ hu
      (fun k m => (W.γD T W.gam m - m) -
        W.π₀ • (cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • m)) y₀
    have hrec : ∀ k : ℕ, k < (Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).length →
        W.π₀ • (s (k + 1) + cO ((Formalism.MainNotions.RamifiedCoefficientChains.xListL W T i (Mi i) (hi i) y' Y).getD k 0) • s k) =
          W.γD T W.gam (s k) - s k := by
      intro k _
      rw [smul_add, hs]
      abel
    exact ⟨s, hs0, hrec, hm hA T Mi hi hT hJ ug hug hv cO hcO i y' Y y₀ hyY hY hδ s hs0 hrec⟩

end Core

theorem semisimpleProductTheorem_iff_dssMem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) :
    Formalism.MainNotions.UnusedSlot35.SemisimpleProductTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →
      ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
        DssMem ((HW l).W K s LL h)) := by
  constructor
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (coreDss_iff_mem _ h9).1 (h hAdm l K s LL hG)
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (coreDss_iff_mem _ h9).2 (h hAdm l K s LL hG)

theorem semisimple_letter_iff_forall_mem (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW)
    (Cm : CmpOf D.loc D.locA HW F) :
    Formalism.MainNotions.UnusedSlot35.SemisimpleLetterTheorem D HW F Cm ↔ (Formalism.MainNotions.UnusedSlot35.AdmDss D HW F Cm →
      ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL),
        DssLetMem ((HW l).W K s LL h)) := by
  constructor
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (dssLet_iff_mem _ h9).1 (h hAdm l K s LL hG)
  · intro h hAdm l _ K s LL hG
    have h9 : Formalism.MainNotions.DeltaInvariantLattices.P9W ((HW l).W K s LL hG) := hAdm.2.2.2.1 l K s LL hG
    exact (dssLet_iff_mem _ h9).2 (h hAdm l K s LL hG)

end Formalism.MainNotions.UnusedSlot35.DssRec
end
end

-- bundled from Formalism.SharpRestriction.LevelLetterCocycles.TwGuard
section
noncomputable section

namespace Formalism.MainNotions

open NumberField IsDedekindDomain Formalism.BasicNotions

def PlaceLiesOver (D : D7) (w' : D.what₂.places.Pl) (v : HeightOneSpectrum (𝓞 D.LL0)) : Prop :=
  ∀ x : 𝓞 D.LL0, 0 < D.what₂.places.val w' ((x : D.LL0) : D.what₂.LL) ↔ x ∈ v.asIdeal

def SetAt (D : D7) (i : D.ntw.Tw) (v : HeightOneSpectrum (𝓞 D.LL0)) : Prop :=
  ∀ x : 𝓞 D.LL0, (∃ y ∈ IsLocalRing.maximalIdeal (D.ntw.O0 i),
      algebraMap (D.ntw.O0 i) (FractionRing (D.ntw.O0 i)) y = D.ntw.emb0 i (x : D.LL0)) ↔ x ∈ v.asIdeal

theorem nonzeroIndexPlace_iff_exists_setAt (D : D7) (W : Set (HeightOneSpectrum (𝓞 D.LL0)))
    (hW : ∀ w', D.what₂.muAt w' ≠ D.what₂.mu0 ↔ ∃ v ∈ W, PlaceLiesOver D w' v)
    (hExt : ∀ v ∈ W, ∃ w', PlaceLiesOver D w' v) (i : D.ntw.Tw) :
    D.ntw.NonzeroIndexPlace i ↔ ∃ v ∈ W, SetAt D i v := by
  constructor
  · rintro ⟨w', hmu, hx⟩
    obtain ⟨v, hv, hov⟩ := (hW w').1 hmu
    exact ⟨v, hv, fun x => (hx x).trans (hov x)⟩
  · rintro ⟨v, hv, hs⟩
    obtain ⟨w', hov⟩ := hExt v hv
    exact ⟨w', (hW w').2 ⟨v, hv, hov⟩, fun x => (hs x).trans (hov x).symm⟩

abbrev integersBaseMap (D : D7) : 𝓞 D.LL0 →+* 𝓞 D.what₂.LL := RingOfIntegers.mapRingHom D.LL0.val.toRingHom

theorem integersBaseMap_coe (D : D7) (x : 𝓞 D.LL0) :
    algebraMap (𝓞 D.what₂.LL) D.what₂.LL (integersBaseMap D x) = ((x : D.LL0) : D.what₂.LL) := rfl

theorem integersBaseMap_injective (D : D7) : Function.Injective (integersBaseMap D) := by
  intro a b h
  have h1 := congrArg (algebraMap (𝓞 D.what₂.LL) D.what₂.LL) h
  rw [integersBaseMap_coe, integersBaseMap_coe] at h1
  exact FaithfulSMul.algebraMap_injective (𝓞 D.LL0) D.LL0 (Subtype.ext h1)

theorem vAdd_pos_iff_mem {K : Type} [Field K] [NumberField K] (la : HeightOneSpectrum (𝓞 K)) {a : 𝓞 K}
    (ha : a ≠ 0) : 0 < vAdd la (a : K) ↔ a ∈ la.asIdeal := by
  have h0 : la.valuation K (a : K) ≠ 0 := by
    rw [Ne, Valuation.zero_iff]
    exact_mod_cast ha
  have hle := la.valuation_le_one (K := K) a
  have hlt : la.valuation K (algebraMap (𝓞 K) K a) < 1 ↔ a ∈ la.asIdeal := la.valuation_lt_one_iff_mem a
  unfold vAdd
  constructor
  · intro h
    by_contra hm
    have h1 : la.valuation K (a : K) = 1 := le_antisymm hle (not_lt.1 fun h' => hm (hlt.1 h'))
    rw [h1] at h
    simp at h
  · intro hm
    have h2 : la.valuation K (a : K) < 1 := hlt.2 hm
    have h3 := (WithZero.log_lt_log h0 one_ne_zero).2 h2
    simp at h3
    omega

theorem exists_placeOver_of_place (D : D7) (v : HeightOneSpectrum (𝓞 D.LL0)) : ∃ w', PlaceLiesOver D w' v := by
  letI : Algebra (𝓞 D.LL0) (𝓞 D.what₂.LL) := (integersBaseMap D).toAlgebra
  haveI hint : Algebra.IsIntegral (𝓞 D.LL0) (𝓞 D.what₂.LL) :=
    ⟨fun x => (Algebra.IsIntegral.isIntegral (R := ℤ) x).tower_top⟩
  obtain ⟨Q, -, hQ, hQv⟩ := Ideal.exists_ideal_over_prime_of_isIntegral v.asIdeal (⊥ : Ideal (𝓞 D.what₂.LL)) (by
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    have : x = 0 := integersBaseMap_injective D (by rw [map_zero]; exact hx)
    rw [this]; exact Ideal.zero_mem _)
  have hQ0 : Q ≠ ⊥ := by
    rintro rfl
    apply v.ne_bot
    rw [← hQv, eq_bot_iff]
    intro x hx
    rw [Ideal.mem_comap, Ideal.mem_bot] at hx
    rw [Ideal.mem_bot]
    exact integersBaseMap_injective D (by rw [map_zero]; exact hx)
  let P : HeightOneSpectrum (𝓞 D.what₂.LL) := ⟨Q, hQ, hQ0⟩
  refine ⟨D.plEq.symm P, fun x => ?_⟩
  have hmem : x ∈ v.asIdeal ↔ integersBaseMap D x ∈ Q := by
    rw [← hQv, Ideal.mem_comap]
    rfl
  by_cases hx : x = 0
  · subst hx
    simp only [ZeroMemClass.coe_zero, map_zero, Submodule.zero_mem, iff_true]
    rw [AddValuation.map_zero]
    exact WithTop.coe_lt_top (0 : ℤ)
  · have hx' : ((x : D.LL0) : D.what₂.LL) ≠ 0 := by
      intro h
      apply hx
      apply integersBaseMap_injective D
      apply FaithfulSMul.algebraMap_injective (𝓞 D.what₂.LL) D.what₂.LL
      rw [integersBaseMap_coe, h, map_zero, map_zero]
    rw [D.val_eq _ _ hx', Equiv.apply_symm_apply, hmem, ← integersBaseMap_coe]
    have hne : integersBaseMap D x ≠ 0 := fun h => hx (integersBaseMap_injective D (by rw [h, map_zero]))
    rw [WithTop.coe_pos]
    exact vAdd_pos_iff_mem P hne

theorem inNonzeroPlaces_recursive_iff (D : D7) (W : Set (HeightOneSpectrum (𝓞 D.LL0)))
    (hW : ∀ w', D.what₂.muAt w' ≠ D.what₂.mu0 ↔ ∃ v ∈ W, PlaceLiesOver D w' v) (i : D.ntw.Tw) :
    D.ntw.NonzeroIndexPlace i ↔ ∃ v ∈ W, SetAt D i v :=
  nonzeroIndexPlace_iff_exists_setAt D W hW (fun v _ => exists_placeOver_of_place D v) i

end Formalism.MainNotions

end
end

