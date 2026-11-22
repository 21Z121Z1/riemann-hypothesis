import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0049
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Alternates
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.FrobeniusOrbits.HostCorollaries
import Development.AbelianVarietyTheory.BlockTheory.ThetaLiftGeometry.Bundle0003
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.TateDualCrystalline
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0046
import Formalism.SharpRestriction.LevelLetterCocycles.QuotientHomNonvanishingBound
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.NotDvdCondN

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ScaleLogMulLeSizeRatioStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.scale_log_mul_le_size_ratio : ∀ eps C A : ℝ, 0 < eps → 0 ≤ C → 0 ≤ A → ∃ x0 : ℝ, ∀ s : Scale, s.eps = eps → x0 ≤ s.x → C * (A * Real.log s.x + 1) * s.b' ≤ s.b := by
  first | exact @GlobalTheory.scale_log_mul_b'_le_b | exact GlobalTheory.scale_log_mul_b'_le_b | (intros; apply GlobalTheory.scale_log_mul_b'_le_b <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.SecondTwistSmallIffExactlyAtAndFinClause
section
noncomputable section

namespace GlobalTheory.Cmp.SmallJumps

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.FrobeniusOrbits GlobalTheory.HTW Module
open GlobalTheory.IndefiniteRowSideFullHecke

theorem finite_of_jumps {L M : Type} [Field L] [AddCommGroup M] [Module L M] (F : ℤ → Submodule L M)
    (U : Submodule L M) (anti : ∀ a, F (a + 1) ≤ F a) (exh : ∀ x ∈ U, ∃ a, x ∈ F a)
    (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, (finrank L (F a) : ℤ) - finrank L (F (a + 1)) = (J.count a : ℤ)) :
    FiniteDimensional L U := by
  have hA : Antitone F := antitone_int_of_succ_le anti
  have hd : Antitone fun a => finrank L (F a) := antitone_int_of_succ_le fun a => by
    have := h a
    omega
  obtain ⟨a₀, ha₀⟩ := Multiset.exists_mem_of_ne_zero hJ
  have hpos : 0 < finrank L (F a₀) := by
    have := h a₀
    have := Multiset.count_pos.2 ha₀
    omega
  have hfin : ∀ a ≤ a₀, FiniteDimensional L (F a) := fun a ha =>
    Module.finite_of_finrank_pos (lt_of_lt_of_le hpos (hd ha))
  obtain ⟨b, hb⟩ := J.toFinset.bddBelow
  have hb' : ∀ a ∈ J, b ≤ a := fun a ha => hb (by simpa using ha)
  have hb0 : b ≤ a₀ := hb' a₀ ha₀
  have hst : ∀ a ≤ b, F a = F b := by
    intro a ha
    induction a, ha using Int.le_induction_down with
    | base => rfl
    | pred a ha ih =>
      haveI := hfin (a - 1) (by omega)
      have h1 := h (a - 1)
      have h2 : J.count (a - 1) = 0 := Multiset.count_eq_zero.2 fun hm => by
        have := hb' _ hm
        omega
      rw [sub_add_cancel, h2] at h1
      rw [← ih]
      exact (Submodule.eq_of_le_of_finrank_eq (hA (by omega)) (by omega)).symm
  haveI := hfin b hb0
  refine Submodule.finiteDimensional_of_le (S₂ := F b) fun x hx => ?_
  obtain ⟨a, ha⟩ := exh x hx
  rcases le_total a b with hab | hab
  · rwa [← hst a hab]
  · exact hA hab ha

section Periods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem filV_anti : Antitone fun a => FilV PD (LL := LL) (V := V) a := by
  refine antitone_int_of_succ_le fun a => ?_
  rintro _ ⟨y, rfl⟩
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul v b => exact ⟨v ⊗ₜ ⟨b.1, PD.Fil_anti a b.2⟩, rfl⟩
  | add x y hx hy => rw [map_add]; exact Submodule.add_mem _ hx hy

theorem filV_exh (x : TensorProduct Qp V BdR) : ∃ a, x ∈ FilV PD (LL := LL) (V := V) a := by
  induction x using TensorProduct.induction_on with
  | zero => exact ⟨0, Submodule.zero_mem _⟩
  | tmul v b =>
    obtain ⟨a, ha⟩ := PD.Fil_exh b
    exact ⟨a, v ⊗ₜ ⟨b, ha⟩, rfl⟩
  | add x y hx hy =>
    obtain ⟨a, ha⟩ := hx
    obtain ⟨b, hb⟩ := hy
    exact ⟨min a b, Submodule.add_mem _ (filV_anti PD (min_le_left a b) ha)
      (filV_anti PD (min_le_right a b) hb)⟩

theorem finite_ddRE_of_multV (ρ : Representation LL G V) (τ : K →ₐ[Qp] LL) (J : Multiset ℤ) (hJ : J ≠ 0)
    (h : ∀ a, multV PD ρ τ a = (J.count a : ℤ)) : FiniteDimensional LL (DdRE PD ρ τ) :=
  finite_of_jumps (FildR PD ρ τ) _
    (fun a => inf_le_inf_left _ (filV_anti PD (by omega : a ≤ a + 1)))
    (fun x hx => (filV_exh PD (LL := LL) x).imp fun _ ha => ⟨hx, ha⟩) J hJ h

end Periods

theorem linearIndepOn_of_invariant {K F W G ι : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (v : ι → W) (hv : ∀ g i, σ g (v i) = v i)
    (s : Finset ι) (h : LinearIndepOn K v s) : LinearIndepOn F v s := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert x s hx ih =>
    have hx' : x ∉ (s : Set ι) := hx
    rw [Finset.coe_insert, linearIndepOn_insert hx'] at h ⊢
    refine ⟨ih h.1, fun hm => h.2 ?_⟩
    obtain ⟨c, hc⟩ := (Submodule.mem_span_image_finset_iff_exists_fun' F).1 hm
    have key : ∀ i ∈ s, ∀ g, a g (c i) = c i := by
      intro i hi g
      have h1 : ∑ i ∈ s, a g (c i) • v i = v x := by
        rw [← hv g x, ← hc, map_sum]
        exact Finset.sum_congr rfl fun j _ => by rw [hσ, hv]
      have h2 := linearIndepOn_finset_iff.1 (ih h.1) (fun j => a g (c j) - c j) (by
        simp only [sub_smul, Finset.sum_sub_distrib, h1, hc, sub_self]) i hi
      exact sub_eq_zero.1 h2
    rw [← hc]
    refine Submodule.sum_mem _ fun i hi => ?_
    obtain ⟨k, hk⟩ := hinv _ (key i hi)
    rw [← hk, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, hi, rfl⟩)

theorem finite_of_invariant {K F W G : Type} [Field K] [Field F] [Algebra K F] [AddCommGroup W]
    [Module F W] [Module K W] [IsScalarTower K F W] [Module.Finite F W] (a : G → F → F) (σ : G → W →+ W)
    (hσ : ∀ g b w, σ g (b • w) = a g b • σ g w)
    (hinv : ∀ b, (∀ g, a g b = b) → ∃ c, algebraMap K F c = b) (U : Submodule K W)
    (hU : ∀ x ∈ U, ∀ g, σ g x = x) : Module.Finite K U := by
  rw [← Module.rank_lt_aleph0_iff]
  refine lt_of_le_of_lt (rank_le (n := finrank F W) fun s hs => ?_) (Cardinal.natCast_lt_aleph0)
  have h1 : LinearIndepOn K (fun x : U => (x : W)) s := hs.map' U.subtype U.ker_subtype
  have h2 := linearIndepOn_of_invariant a σ hσ hinv (fun x : U => (x : W))
    (fun g x => hU x x.2 g) s h1
  simpa using LinearIndependent.fintype_card_le_finrank h2

section FieldPeriods

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    (PD : PeriodData G Qp K₀ K B BdR)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]

theorem finite_ddR_of_isField (hF : IsField BdR) [Module.Finite Qp V] (ρ : Representation LL G V) :
    Module.Finite LL (DdR PD ρ) := by
  letI : Field BdR := hF.toField
  haveI := PD.finK
  let σ : G → TensorProduct Qp BdR V →ₗ[Qp] TensorProduct Qp BdR V := fun g =>
    TensorProduct.map (((PD.actdR g).toAlgHom.toLinearMap).restrictScalars Qp) ((ρ g).restrictScalars Qp)
  have hσ : ∀ g (b : BdR) w, σ g (b • w) = PD.actdR g b • σ g w := by
    intro g b w
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, TensorProduct.smul_tmul']
    | add x y hx hy => simp only [smul_add, map_add, hx, hy]
  let U : Submodule K (TensorProduct Qp BdR V) :=
    { carrier := {x | ∀ g, σ g x = x}
      zero_mem' := fun g => map_zero _
      add_mem' := fun hx hy g => by rw [map_add, hx g, hy g]
      smul_mem' := fun c x hx g => by
        rw [← algebraMap_smul BdR c x, hσ, hx g, AlgEquiv.commutes] }
  haveI : Module.Finite K U := finite_of_invariant (F := BdR) (fun g b => PD.actdR g b)
    (fun g => (σ g).toAddMonoidHom) hσ PD.invdR U fun _ hx => hx
  haveI : Module.Finite Qp U := Module.Finite.trans K U
  have hc : ∀ g x, σ g (TensorProduct.comm Qp V BdR x) =
      TensorProduct.comm Qp V BdR (actVdR PD ρ g x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul c v => simp [σ, actVdR]
    | add x y hx hy => simp only [map_add, hx, hy]
  let f : DdR PD ρ →ₗ[Qp] U :=
    { toFun := fun x => ⟨TensorProduct.comm Qp V BdR x, fun g => by
        have := x.2
        simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
          LinearMap.id_apply, sub_eq_zero] at this
        rw [hc, this g]⟩
      map_add' := fun x y => Subtype.ext (map_add _ _ _)
      map_smul' := fun c x => Subtype.ext (map_smul (TensorProduct.comm Qp V BdR) c _) }
  haveI : Module.Finite Qp (DdR PD ρ) := Module.Finite.of_injective f fun x y h =>
    Subtype.ext ((TensorProduct.comm Qp V BdR).injective (congrArg Subtype.val h))
  exact Module.Finite.of_restrictScalars_finite Qp LL _

end FieldPeriods

variable (D : D7)

section Place

variable (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i))

theorem over_iff (τ : BlockSumMultiplicities.Emb D i w hw) (g : D.R.GG) :
    BlockSumMultiplicities.Over D i w hw τ g ↔ CrystallineAtPlaces.Reads D i w hw τ g := by
  refine forall_congr' fun x => ⟨?_, fun h => ⟨_, h.symm, CrystallineAtPlaces.embLL_sigmaOf g x⟩⟩
  rintro ⟨y, h1, h2⟩
  have : y = D.embE (D.host.sigmaOf g x) :=
    D.what₂.embLL.injective (h2.trans (CrystallineAtPlaces.embLL_sigmaOf g x).symm)
  rw [← this, h1]

variable {k : ℕ} (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i))

theorem mult_eq (τ : BlockSumMultiplicities.Emb D i w hw) (a : ℤ) :
    BlockSumMultiplicities.mult D i w hw M τ a = CrystallineAtPlaces.mult D i w hw M τ a := rfl

end Place

def FinClause : Prop :=
  ∀ (i : D.nd.Loc) (r : BlockSumMultiplicities.Fam D i D.R.nV) (ρ : BlockSumMultiplicities.Fam D i D.R.r) (π : D.nd.X i),
    BlockSumMultiplicities.HidaSetting D i r ρ π → ∀ w hw (τ : BlockSumMultiplicities.Emb D i w hw),
      BlockSumMultiplicities.FinDR D i w hw (T2O D.nd i ρ π) τ

variable {D}

def JumpsByLetterAt (L : SizeData₂ D) (ε : ℤˣ) : Prop :=
  ∀ (i : D.nd.Loc) (r : BlockSumMultiplicities.Fam D i D.R.nV) (ρ : BlockSumMultiplicities.Fam D i D.R.r) (π : D.nd.X i),
    CrystallineAtPlaces.HidaSetting D i r ρ π →
    ∀ (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)),
      CrystallineAtPlaces.CrysInput D i w hw r → CrystallineAtPlaces.JumpInput D i w hw ε r →
      CrystallineAtPlaces.CrysAt D i w hw (T2O D.nd i ρ π) ∧
      ∀ τ g, CrystallineAtPlaces.Reads D i w hw τ g →
        CrystallineAtPlaces.HasJumps D i w hw (T2O D.nd i ρ π) τ
          (jT2 (hcAt D g) (CrystallineAtPlaces.liftIdx D i) (pos ε g)) ∧
        ((etaHat L : ℤ) < szT (hcAt D g) (CrystallineAtPlaces.liftIdx D i) (pos ε g) →
          CrystallineAtPlaces.countIn D i w hw (T2O D.nd i ρ π) τ (etaHat L) = D.R.m)

end GlobalTheory.Cmp.SmallJumps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.ThinSizeDominatesAtLargeScaleStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.thinSize_dominates_at_large_scale : ∀ eps : ℝ, 0 < eps → ∃ x0 : ℝ, ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), L.sc.eps = eps → x0 ≤ L.sc.x → (100 : ℝ) ≤ L.sc.w'' D.R.n ∧ 100 * (L.etaSz + L.Sc + D.R.t + 2) ≤ L.sc.w'' D.R.n ∧ L.sc.w'' D.R.n ≤ L.sc.b' := by
  first | exact @GlobalTheory.HTW.thinSize_dominates | exact GlobalTheory.HTW.thinSize_dominates | (intros; apply GlobalTheory.HTW.thinSize_dominates <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TopSizeAddLeThreeHalvesScaleStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.topSize_add_le_three_halves_scale : ∀ (D : D7) (L : SizeData₂ D) (_ : ParameterChoice' D L), 4 ≤ L.sc.x → ∀ t, (L.bT t : ℝ) + L.sc.b' / L.sc.x ≤ 3 / 2 * L.sc.b' := by
  first | exact @GlobalTheory.Ggeo.bT_add_div_le_three_halves | exact GlobalTheory.Ggeo.bT_add_div_le_three_halves | (intros; apply GlobalTheory.Ggeo.bT_add_div_le_three_halves <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsMemWindowsStatement
section
open GlobalTheory.HTW Formalism.BasicNotions Formalism.FrobeniusOrbits
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.twistedDualJumps_mem_windows : ∀ {R : Ranks} (P : HCParam R) (j : Fin R.m) (s : Bool) (S η : ℝ), (∀ i, 0 ≤ ((P.v i : ℚ) : ℝ) ∧ ((P.v i : ℚ) : ℝ) ≤ S) → (∀ i, |((P.b i - P.e j : ℚ) : ℝ)| ≤ η) → ∀ u ∈ jT1 P j s, (if (!s) = true then szT P j s ≤ u ∧ u ≤ szT P j s + (⌊S⌋₊ : ℕ) else -szT P j s - (⌊S⌋₊ : ℕ) ≤ u ∧ u ≤ -szT P j s) ∨ |u| ≤ ((⌊η⌋₊ + R.t + 2 : ℕ) : ℤ) := by
  first | exact @GlobalTheory.jT1_mem_window_of_bounded_v | exact GlobalTheory.jT1_mem_window_of_bounded_v | (intros; apply GlobalTheory.jT1_mem_window_of_bounded_v <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualJumpsWithoutBlockNodupParameters
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

namespace GlobalTheory.HTW.Rec

section Param

variable {R : Ranks} (P : HCParam R)

theorem v_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.k - 1),
    P.v ⟨a + n + 1, h⟩ < P.v ⟨a, by omega⟩
  | 0, h => (P.u_gt_v ⟨a + 1, h⟩).trans (P.v_gt_u ⟨a, by omega⟩)
  | n + 1, h => by
    have h1 := v_step a n (by omega)
    have h2 : P.v ⟨a + (n + 1) + 1, h⟩ < P.v ⟨a + n + 1, by omega⟩ :=
      (P.u_gt_v ⟨a + (n + 1) + 1, h⟩).trans (P.v_gt_u ⟨a + n + 1, by omega⟩)
    exact h2.trans h1

theorem b_step (a : ℕ) : ∀ (n : ℕ) (h : a + n + 1 < R.m),
    P.b ⟨a, by omega⟩ < P.b ⟨a + n + 1, h⟩
  | 0, h => by
    have h1 := P.gap_be ⟨a, by omega⟩
    have h2 := P.gap_eb ⟨a, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith
  | n + 1, h => by
    have h0 := b_step a n (by omega)
    have h1 := P.gap_be ⟨a + n + 1, by omega⟩
    have h2 : ((R.t : ℚ) + 3) / 2 ≤ P.b ⟨a + (n + 1) + 1, h⟩ - P.e ⟨a + n + 1, by omega⟩ :=
      P.gap_eb ⟨a + n + 1, by omega⟩ h
    have ht : (0 : ℚ) ≤ R.t := by positivity
    linarith

theorem v_lt {a c : Fin (R.k - 1)} (h : a < c) : P.v c < P.v a := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := v_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

theorem b_lt {a c : Fin R.m} (h : a < c) : P.b a < P.b c := by
  obtain ⟨n, hn⟩ := Nat.exists_eq_add_of_lt (show a.1 < c.1 from h)
  have := b_step P a.1 n (hn ▸ c.2)
  convert this using 2
  exact Fin.ext hn

theorem floor_v_inj : Function.Injective fun a : Fin (R.k - 1) => ⌊P.v a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.v_int a
  obtain ⟨y, hy⟩ := P.v_int c
  have hxy : P.v a = P.v c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (v_lt P h).ne'
  · exact h
  · exact absurd hxy (v_lt P h).ne

theorem floor_b_inj : Function.Injective fun a : Fin R.m => ⌊P.b a⌋ := by
  intro a c hac
  obtain ⟨x, hx⟩ := P.b_int a
  obtain ⟨y, hy⟩ := P.b_int c
  have hxy : P.b a = P.b c := by
    simp only [hx, hy, Int.floor_intCast] at hac
    rw [hx, hy, hac]
  rcases lt_trichotomy a c with h | h | h
  · exact absurd hxy (b_lt P h).ne
  · exact h
  · exact absurd hxy (b_lt P h).ne'

theorem cloud_add_lows_nodup (j : Fin R.m) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (cloud P j + lows P j).Nodup := by
  rw [Multiset.nodup_add]
  refine ⟨?_, ?_, ?_⟩
  · refine Multiset.Nodup.map (fun a c h => floor_v_inj P ?_) Finset.univ.nodup
    simpa using h
  · refine Multiset.Nodup.map (fun a c h => floor_b_inj P ?_) Finset.univ.nodup
    simpa using h
  · rw [Multiset.disjoint_left]
    intro u hu hu'
    obtain ⟨a, -, rfl⟩ := Multiset.mem_map.1 hu
    obtain ⟨i, -, hi⟩ := Multiset.mem_map.1 hu'
    obtain ⟨x, hx⟩ := P.v_int a
    obtain ⟨y, hy⟩ := P.b_int i
    have hx0 : 0 ≤ x := by
      have := hv a
      rw [hx] at this
      exact_mod_cast this
    have hy0 : 0 < y := by
      have := hb i
      rw [hy] at this
      exact_mod_cast this
    simp only [hx, hy, Int.floor_intCast] at hi
    omega

theorem twistedDualJumpsWithoutBlock_nodup_of_signs (j : Fin R.m) (s : Bool) (hv : ∀ a, 0 ≤ P.v a) (hb : ∀ i, 0 < P.b i) :
    (jT2 P j s).Nodup := by
  have h := cloud_add_lows_nodup P j hv hb
  have h1 : Function.Injective fun u : ℤ => -u - 1 := fun a c h => by
    have : -a - 1 = -c - 1 := h
    omega
  have h2 : Function.Injective fun u : ℤ => (R.t : ℤ) - 1 - u := fun a c h => by
    have : (R.t : ℤ) - 1 - a = (R.t : ℤ) - 1 - c := h
    omega
  unfold jT2 jW
  refine Multiset.Nodup.map h1 ?_
  cases s
  · simpa using Multiset.Nodup.map h2 h
  · simpa using h

end Param

theorem twistedDualJumpsWithoutBlock_nodup_of_roomy : ∀ {D : D7} (L : SizeData₂ D) (C : ℝ) (j : Fin D.R.m) (g : D.R.GG) (s : Bool),
    Roomy L C → (jT2 (hcAt D g) j s).Nodup := by
  intro D L C j g s hR
  obtain ⟨hC, h100, hη, hwb, -, hCb⟩ := id hR
  have hS := L.Sc_pos
  have hE := L.etaSz_pos
  have ht : (0 : ℝ) ≤ D.R.t := by positivity
  have hηw : L.etaSz < L.sc.w'' D.R.n := by linarith
  have hbig : L.etaSz < (⌊(hcAt D g).e j⌋ : ℝ) := by
    by_cases hT : Thick D.host g
    · have h1 := (SizeThick.size_thick L g j hT).1
      have hL : (0 : ℝ) ≤ (D.host.Lw : ℝ) := by positivity
      have hb' : 0 < L.sc.b' := by linarith
      have h2 : L.sc.b' ≤ C * ((D.host.Lw : ℝ) + 1) * L.sc.b' := by
        have : (1 : ℝ) ≤ C * ((D.host.Lw : ℝ) + 1) := by nlinarith
        nlinarith
      linarith
    · exact lt_of_lt_of_le hηw (size_not_thick L C g j hR hT).1
  refine twistedDualJumpsWithoutBlock_nodup_of_signs _ j s ?_ ?_
  · intro a
    have h := (L.cloud_v (D.eTau.symm ⟨plc g, plc_mem g⟩) a).1
    exact_mod_cast h
  · intro i
    have h := L.be_close (D.eTau.symm ⟨plc g, plc_mem g⟩) i j
    have h' : |((((hcAt D g).b i - (hcAt D g).e j : ℚ)) : ℝ)| ≤ L.etaSz := h
    obtain ⟨z, hz⟩ := (hcAt D g).e_int j
    rw [hz, Int.floor_intCast] at hbig
    rw [hz] at h'
    have h2 := (abs_le.1 h').1
    push_cast at h2
    have : (0 : ℝ) < (((hcAt D g).b i : ℚ) : ℝ) := by linarith
    exact_mod_cast this

end GlobalTheory.HTW.Rec
end

-- bundled from Development.AbelianVarietyTheory.Proofs.SatakeParameters.TwistedDualsEqTateDualsAtEnlargement
section
open NumberField IsDedekindDomain GlobalTheory.HTW GlobalTheory.HTW.Rec Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.FrobeniusOrbits

noncomputable section
namespace GlobalTheory.HTW.Rec

theorem enlLoc_apply {D : D7} {i : D.nd.Loc} {w : HeightOneSpectrum (𝓞 D.host.E)}
    {hw : w ∈ placesOver D.host.E (D.nd.l i)} (C : Enl D i w hw) {k : ℕ}
    (M : GE D.nd →* Matrix (Fin k) (Fin k) (D.nd.O i)) (g : Br.G D.nbr i w hw) (a b : Fin k) :
    C.loc M g a b = C.inc ((D.nbr i w hw).toLL (M (decS D.nd w (Br.iota D.nbr i w hw g)) a b)) := rfl

theorem twistedDuals_eq_tateDuals : ∀ {D : D7} (i : D.nd.Loc) (w : HeightOneSpectrum (𝓞 D.host.E)) (hw : w ∈ placesOver D.host.E (D.nd.l i)) (C : Enl D i w hw) (r : D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (π : D.nd.X i), (∀ s, C.inc ((Br.locChi D.nbr i w hw (epsU D.nd i) s : (Br.LL D.nbr i w hw)ˣ) : Br.LL D.nbr i w hw) = ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 s : (↥C.LL.1)ˣ) : ↥C.LL.1)) → (∀ x, C.loc (rDuO D.nd i r x) = twistM (dualM (C.loc (rTwO D.nd i r x))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1)) ∧ C.loc (T2O D.nd i ρ π) = twistM (dualM (C.loc (WpO D.nd i ρ π))) (cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1) := by
  intro D i w hw C r ρ π h
  have hc : ∀ g, ((cycLL (Br.PD D.loc D.nbr i w hw) ↥C.LL.1 g : (↥C.LL.1)ˣ) : ↥C.LL.1) =
      C.inc ((D.nbr i w hw).toLL ((epsU D.nd i (decS D.nd w (Br.iota D.nbr i w hw g)) : (D.nd.O i)ˣ) : D.nd.O i)) :=
    fun g => (h g).symm
  refine ⟨fun x => ?_, ?_⟩
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, rDuO, rTwO, map_inv, Units.val_mul, map_mul]
    simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, inv_inv, Units.val_mul, map_mul]
    exact congrArg _ (by ring)
  · ext g a b
    rw [enlLoc_apply]
    simp only [twistM, dualM, MonoidHom.coe_mk, OneHom.coe_mk, Matrix.smul_apply, Matrix.transpose_apply, smul_eq_mul, hc, enlLoc_apply, T2O, map_inv, Units.val_mul, map_mul]

end GlobalTheory.HTW.Rec
end
end

