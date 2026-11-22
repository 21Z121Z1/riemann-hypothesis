import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0040
import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.LtChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EqZeroOfInAMul
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsKerPowDvd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0851
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0976
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0938
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.Bundle0021
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0974
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsRootSelectionUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurable
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0038
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroup
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.NotIsCompactUnivFv
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0028
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0027
import Formalism.LocalToGlobal.ProjectiveLattices.Bundle0011
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0074

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LogDifferentialMulLogCoordinateWedge
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory.LogDR.WedgeMul

theorem prod_perm_sign {A : Type} [Ring A] {α : Type} (f : α → A)
    (hf : ∀ a b, f a * f b = -(f b * f a)) {l₁ l₂ : List α} (h : l₁.Perm l₂) :
    ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ (l₁.map f).prod = ε • (l₂.map f).prod := by
  induction h with
  | nil => exact ⟨1, Or.inl rfl, by simp⟩
  | cons x _ ih =>
    obtain ⟨ε, hε, e⟩ := ih
    exact ⟨ε, hε, by simp only [List.map_cons, List.prod_cons, e, mul_smul_comm]⟩
  | swap x y l =>
    refine ⟨-1, Or.inr rfl, ?_⟩
    simp only [List.map_cons, List.prod_cons, ← mul_assoc, hf y x, neg_mul, neg_smul, one_smul]
  | trans _ _ ih₁ ih₂ =>
    obtain ⟨ε₁, h₁, e₁⟩ := ih₁
    obtain ⟨ε₂, h₂, e₂⟩ := ih₂
    refine ⟨ε₁ * ε₂, ?_, by rw [e₁, e₂, smul_smul]⟩
    rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl <;> simp

end GlobalTheory.LogDR.WedgeMul

open GlobalTheory.LogDR.WedgeMul in

theorem GlobalTheory.LogDR.dlog_mul_logWedge : ∀ (K : Type) [Field K] (n : ℕ) (x : Fin n → Kˣ) (i : Fin n) (I : Finset (Fin n)), (i ∈ I → ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = 0) ∧ (i ∉ I → ∃ ε : ℤ, (ε = 1 ∨ ε = -1) ∧ ExteriorAlgebra.ι K (dlog (x i)) * logWedge x I = ε • logWedge x (insert i I)) := by
  intro K _ n x i I
  set f : Fin n → abelian₂ K := fun j => ExteriorAlgebra.ι K (dlog (x j)) with hfdef
  have hf : ∀ a b, f a * f b = -(f b * f a) := fun a b =>
    eq_neg_of_add_eq_zero_left (ExteriorAlgebra.ι_add_mul_swap _ _)
  constructor
  · intro hi
    have hp : (I.sort (· ≤ ·)).Perm (i :: (I.erase i).sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · refine List.nodup_cons.2 ⟨?_, Finset.sort_nodup _ _⟩
        simp
      · by_cases ha : a = i
        · subst ha; simp [hi]
        · simp [ha]
    obtain ⟨ε, -, e⟩ := prod_perm_sign f hf hp
    show f i * ((I.sort (· ≤ ·)).map f).prod = 0
    rw [e, mul_smul_comm, List.map_cons, List.prod_cons, ← mul_assoc]
    simp [hfdef, ExteriorAlgebra.ι_sq_zero]
  · intro hi
    have hp : ((insert i I).sort (· ≤ ·)).Perm (i :: I.sort (· ≤ ·)) := by
      refine (List.perm_ext_iff_of_nodup (Finset.sort_nodup _ _) ?_).2 fun a => ?_
      · exact List.nodup_cons.2 ⟨by simpa using hi, Finset.sort_nodup _ _⟩
      · simp
    obtain ⟨ε, hε, e⟩ := prod_perm_sign f hf hp
    refine ⟨ε, hε, ?_⟩
    show f i * ((I.sort (· ≤ ·)).map f).prod = ε • (((insert i I).sort (· ≤ ·)).map f).prod
    rw [e, List.map_cons, List.prod_cons, smul_smul]
    rcases hε with rfl | rfl <;> simp
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LubinTateFiltrationJumpAtEmbedding
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.PZ GlobalTheory.PMC GlobalTheory.AinfK GlobalTheory.AcrisK

theorem GlobalTheory.LTDegOne.main : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
    ∀ (K LL : FinExt l) (χ : ↥(GK K) →* (↥K.1)ˣ) (π : ↥(OL K)) (z : ℕ → Om l), LTData K χ π z →
    ∀ τ₀ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1, ∃ x ∈ DdRE (P.PD K) (lineRep (K := K) (LL := LL) (ltChar τ₀ χ⁻¹)) τ₀, x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 1 ∧
      x ∉ FilV (P.PD K) (LL := ↥LL.1) (V := Fin 1 → ↥LL.1) 2 := by
  intro l _ P AI hT K LL χ π z hLT τ₀
  obtain ⟨ω, t, u, hω0, hω2, ht, hg⟩ := GlobalTheory.T.exists_lubin_tate_period_element l K χ π z hLT
  obtain ⟨Ψ, hK, hG, h0, h1, h2⟩ := GlobalTheory.T.period_ring_embedding_properties l P AI hT K
  have hX1 : Ψ (toB K (ofA K ω)) ∈ (P.PD K).Fil 1 := h1 ω hω0
  have hX2 : Ψ (toB K (ofA K ω)) ∉ (P.PD K).Fil 2 := h2 ω hω0 hω2
  have hXU : Ψ (toB K (ofA K ω)) * Ψ u ∈ (P.PD K).Fil 1 := by
    simpa using (P.PD K).Fil_mul 1 0 _ _ hX1 (h0 u)
  have hXXU : Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) ∈ (P.PD K).Fil 2 := by
    simpa [one_add_one_eq_two] using (P.PD K).Fil_mul 1 1 _ _ hX1 hXU
  have hY : Ψ t = Ψ (toB K (ofA K ω)) + Ψ (toB K (ofA K ω)) * (Ψ (toB K (ofA K ω)) * Ψ u) := by
    rw [ht, map_mul, map_add, map_one, map_mul]; ring
  refine GlobalTheory.T.lubin_tate_period_filtration_exact l P K LL χ τ₀ (Ψ t) (fun g => ?_) ?_ ?_
  · rw [hG, hg, map_mul, hK]
  · rw [hY]
    exact add_mem hX1 ((P.PD K).Fil_anti 1 (by simpa [one_add_one_eq_two] using hXXU))
  · intro h
    apply hX2
    have := sub_mem h hXXU
    rwa [hY, add_sub_cancel_right] at this
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MLatAnyLevelOfFullLattice
section
noncomputable section

namespace GlobalTheory.GoodLat.Road

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.IndefR.Arith Formalism.IndefR.FWT
open GlobalTheory.IndefiniteRowSideFullHecke.GoodBasisCentralIdempotents GlobalTheory.IndefiniteRowSideFullHecke.SupremumLattice

abbrev kapRows (D : D7) : Rows.Data D.R :=
  { D.what₂ with
    kaBig := fun j τ i => (DV.aPlusQ_int D j τ i).choose
    kaSmall := fun j τ c => -(DV.aMinusQ_int D j τ c).choose }

set_option maxHeartbeats 4000000 in

def kapRec (D : D7) : D7 :=
  { D with
    what₂ := kapRows D
    nd := { D.nd with }
    ntw := { D.ntw with }
    naut := { D.naut with }
    nbc := { D.nbc with }
    nexp := { D.nexp with }
    ntypes := { D.ntypes with }
    nth := { D.nth with } }

theorem kapDef_kapRec (D : D7) : DV.KapDef (kapRec D) := fun j _ _ τ =>
  ⟨fun i => (DV.aPlusQ_int D j τ i).choose_spec.symm, fun c => by
    show ((-(DV.aMinusQ_int D j τ c).choose : ℤ) : ℚ) = -DV.aMinusQ D j τ c
    rw [Int.cast_neg, ← (DV.aMinusQ_int D j τ c).choose_spec]⟩

def kapCore {D : D7} (T : Core D) : Core (kapRec D) :=
  { T with Q := { T.Q with } }

theorem volPair_kapRec (D : D7) (V : TH.HSp D) : volPair (D := kapRec D) V = volPair (D := D) V := by
  unfold volPair; rfl

theorem muQ_kapRec (D : D7) (V : TH.HSp D) : muQ (D := kapRec D) V = muQ (D := D) V :=
  congrArg (fun p : MeasureTheory.Measure (Formalism.L2.Theta.GA D V) × Set (Formalism.L2.Theta.GA D V) =>
    (p.1.restrict p.2).map (autMk (D := D) V)) (volPair_kapRec D V)

open Classical in
theorem muQ1_congr_datum (D : D7) (V : TH.HSp D) : muQ1 (D := kapRec D) V = muQ1 (D := D) V :=
  congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) =>
    if μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤ then (μ Set.univ)⁻¹ • μ else MeasureTheory.Measure.dirac (autMk (D := D) V 1))
    (muQ_kapRec D V)

theorem finVol_kapRec {D : D7} {V : TH.HSp D} (h : FinVol (D := D) V) : FinVol (D := kapRec D) V :=
  (congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) => μ Set.univ ≠ 0 ∧ μ Set.univ ≠ ⊤)
    (muQ_kapRec D V)).mpr h

theorem memLp_kapRec {D : D7} {V : TH.HSp D} {φ : AutQ (D := D) V → ℂ}
    (h : MeasureTheory.MemLp φ 2 (muQ1 (D := D) V)) : MeasureTheory.MemLp φ 2 (muQ1 (D := kapRec D) V) :=
  (congrArg (fun μ : MeasureTheory.Measure (AutQ (D := D) V) => MeasureTheory.MemLp φ 2 μ) (muQ1_congr_datum D V)).mpr h

theorem norm_toLp_congr {α : Type} [MeasurableSpace α] {μ ν : MeasureTheory.Measure α} (e : μ = ν) {φ : α → ℂ}
    (h : MeasureTheory.MemLp φ 2 μ) (h' : MeasureTheory.MemLp φ 2 ν) : ‖h.toLp φ‖ = ‖h'.toLp φ‖ := by
  subst e; rfl

section Readings

variable {D : D7} {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} {Comp : Type} (V : TH.HSp D)
  {K : Type} [Field K] {C : Type} [AddCommGroup C] [Module K C] (σ : K →+* ℂ)
  {X : Comp → ReciprocityTheory.ChartRestriction.G.FD.Data E r} (rd : C →ₛₗ[σ] FDSec X)
  (dict : Formalism.L2.Theta.GA D V → Σ c, ReciprocityTheory.ChartRestriction.G.FD.Frame (X c).Ψ r) (mu : Formalism.L2.Theta.GA D V → ℂ)

theorem j_mem_l2_under_datum_change (h : JMemL2 (D := D) V σ rd dict mu) : JMemL2 (D := kapRec D) V σ rd dict mu := fun f =>
  memLp_kapRec (φ := jFn (D := D) V σ rd dict mu f) (h f)

theorem jMemL2_congr_datum (h : JMemL2 (D := D) V σ rd dict mu) (h' : JMemL2 (D := kapRec D) V σ rd dict mu)
    (hd : L2Definite (D := D) V σ rd dict mu h) : L2Definite (D := kapRec D) V σ rd dict mu h' := fun f h0 =>
  hd f ((norm_toLp_congr (φ := jFn (D := D) V σ rd dict mu f) (muQ1_congr_datum D V) (h' f) (h f)).symm.trans h0)

end Readings

theorem cusp_l2_under_datum_change {D : D7} {T : Core D} (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) : CuspL2 (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) := fun a n hd =>
  j_mem_l2_under_datum_change (D := D) (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) (h.cuspidalL2Subspace j hj σ hσ a n hd)

theorem cuspL2_congr_core_of_lawsM {D : D7} {T : Core D} (h : LawsM T) (j : ℕ) (hj : InR D j) (σ : T.Q.c.F →+* ℂ)
    (hσ : GoodEmb T.Q.c σ) (h' : CuspL2 (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ)) :
    L2DefiniteCuspForms (D := kapRec D) (T.U j) σ (T.V j σ) (T.dict j σ) (T.mu j σ) h' := fun a n hd =>
  jMemL2_congr_datum (D := D) (T.V j σ) σ (rdC (T.U j) σ a n) (T.dict j σ) (T.mu j σ) _ (h' a n hd)
    (h.l2Def j hj σ hσ a n hd)

set_option maxHeartbeats 1000000 in

theorem lawsM_kapCore {D : D7} {T : Core D} (h : LawsM T) : LawsM (kapCore T) where
  pins := h.pins
  half := h.half
  evalWD := h.evalWD
  unf := h.unf
  unTest := h.unTest
  chiTriv := h.chiTriv
  dictU := h.dictU
  spaceW := h.spaceW
  levelK := h.levelK
  xiAbs := h.xiAbs
  muUnit := h.muUnit
  muCont := h.muCont
  finVol j hj σ hσ := finVol_kapRec (D := D) (V := T.V j σ) (h.finVol j hj σ hσ)
  cuspFD := h.cuspFD
  supDef := h.supDef
  cuspidalL2Subspace j hj σ hσ := cusp_l2_under_datum_change (D := D) (T := T) h j hj σ hσ
  l2Def j hj σ hσ := cuspL2_congr_core_of_lawsM (D := D) (T := T) h j hj σ hσ _
  unitIndep := h.unitIndep
  ptNe := h.ptNe

theorem wtA_eq {D : D7} {j : ℕ} (hj : InR D j) {w : WeightFamilies.Wt D j} (hw : IsKappa D j w) (hn : Even D.R.nV) :
    kappaExp (kapRec D) (kapDef_kapRec D) hn j = wtA w := by
  obtain ⟨-, h⟩ := isKappa_kaWt (D := kapRec D) (kapDef_kapRec D) hn hj
  have hP : (DIV.Cons.kaWt (kapRec D) (kapDef_kapRec D) hn j).aP = w.aP := by
    funext τ i
    exact_mod_cast ((h τ).1 i).trans ((hw.2 τ).1 i).symm
  have hM : (DIV.Cons.kaWt (kapRec D) (kapDef_kapRec D) hn j).aM = w.aM := by
    funext τ c
    obtain ⟨c, rfl⟩ := Fin.rev_surjective c
    exact_mod_cast ((h τ).2 c).trans ((hw.2 τ).2 c).symm
  funext x
  unfold kappaExp wtA
  rw [hP, hM]
  rfl

set_option maxHeartbeats 1000000 in
theorem supLatticeFullAt_kapCore {D : D7} (T : Core D) (j : ℕ) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n : ℕ) :
    SupLatticeFullAt (kapCore T) j a n ↔ SupLatticeFullAt T j a n := Iff.rfl

theorem fullLat_of_kappa (H : IntegralCuspFormsFullLattice) {D : D7} (T : Core D) (hT : LawsM T) {j : ℕ} (hj : InR D j)
    {w : WeightFamilies.Wt D j} (hw : IsKappa D j w) :
    FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c)) fun la => isVal_valSet la := by
  have hn : Even D.R.nV := hw.1 ▸ w.n_even
  have h := H (kapRec D) (kapDef_kapRec D) hn (kapCore T) (lawsM_kapCore hT) j hj
  have h' := (supLatticeFullAt_kapCore T j _ _).1 h
  rw [wtA_eq hj hw hn] at h'
  have h'' : SupLatticeFullAt T j (wtA w) w.n := by rw [hw.1]; exact h'
  exact (supIn_full_iff _ _ _).1 h''

section Abstract

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]

omit [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [Fintype G] in

theorem isKsForm_of_isBaseChange (A : FormsL LL Ks WL W G) {C : Type} [AddCommGroup C] [Module Ks C]
    [FiniteDimensional Ks C] (ι : C →ₗ[Ks] WL) (hι : IsBaseChange LL ι) (hW : A.WK = LinearMap.range ι) :
    A.IsKsForm := by
  let b := Module.finBasis Ks C
  let B := (Algebra.TensorProduct.basis LL b).map hι.equiv
  have e : ∀ i, B i = ι (b i) := fun i => by
    simp [B, Algebra.TensorProduct.basis_apply]
  have e' : (fun i => ι (b i)) = B := funext fun i => (e i).symm
  refine ⟨_, fun i => ι (b i), fun i => hW ▸ ⟨b i, rfl⟩, ?_, ?_, e' ▸ B.linearIndependent, e' ▸ B.span_eq⟩
  · rw [e']
    exact B.linearIndependent.restrict_scalars' Ks
  · show Submodule.span Ks (Set.range (ι ∘ b)) = _
    rw [Set.range_comp, Submodule.span_image, b.span_eq, Submodule.map_top, hW]

theorem mjFull_of_full (A : FormsL LL Ks WL W G) (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G)
    (lam0 : J0 →* LLˣ) (eC : G → LL) : MjFull A J0 lam0 eC := by
  refine ⟨?_, fun d b hb => isLattice_Mcoord A hK hM J0 lam0 eC b hb.1 fun i =>
    hb.2 ▸ Submodule.subset_span ⟨i, rfl⟩⟩
  obtain ⟨n, b, -, -, -, h3, h4⟩ := hK
  have : FiniteDimensional LL WL := (Module.Basis.mk h3 h4.ge).finiteDimensional_of_finite
  infer_instance

end Abstract

section Comparison₂

variable {D : D7} (T : Core D) (j : ℕ) (w : WeightFamilies.Wt D j)
variable {LL : Type} [Field LL] [NumberField LL] [Algebra T.Q.c.F LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module T.Q.c.F WL] [IsScalarTower T.Q.c.F LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 T.Q.c.F) WL] [IsScalarTower (𝓞 T.Q.c.F) T.Q.c.F WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G : Type} [Group G] [Fintype G]

theorem mjFull_of_fullLat (A : FormsL LL T.Q.c.F WL W G) (ι : Cusp T j w →ₗ[T.Q.c.F] WL) (hA : CarriesCusp T j w A ι)
    (hl : FullLat (T.cuspA j (wtA w) w.n) (valSet (T.Q.Xo j) T.Q.c (algCls (T.Q.Xo j) T.Q.c))
      fun la => isVal_valSet la)
    (J0 : Subgroup G) (lam0 : J0 →* LLˣ) (eC : G → LL) : MjFull A J0 lam0 eC := by
  obtain ⟨hι, hW, hN⟩ := hA
  have hfd : FiniteDimensional T.Q.c.F (Cusp T j w) := by
    obtain ⟨s, hs⟩ := hl.fg
    refine ⟨s, ?_⟩
    rw [← hl.span_eq_top, ← hs, Submodule.span_span_of_tower]
  refine mjFull_of_full A (isKsForm_of_isBaseChange A ι hι hW) (mkFull_of A ι hW (fun x => ?_) hl) J0 lam0 eC
  constructor
  · rintro ⟨hx, h⟩
    obtain ⟨f, rfl⟩ := hW ▸ hx
    exact ⟨f, fun la v hv => (T.nrmM_le_one_iff j la ⟨v, hv⟩ _).1 ((hN la f hx).1 (h la) ⟨v, hv⟩), rfl⟩
  · rintro ⟨f, hf, rfl⟩
    have hx : ι f ∈ A.WK := hW ▸ ⟨f, rfl⟩
    exact ⟨hx, fun la => (hN la f hx).2 fun y => (T.nrmM_le_one_iff j la y _).2 (hf la y.1 y.2)⟩

end Comparison₂

theorem mLatAnyLevel_of_fullLattice (H : IntegralCuspFormsFullLattice) : MLatAnyLevel := by
  intro D T hT j hj w hw LL _ _ _ WL _ _ _ _ _ _ _ _ W _ _ G _ _ A ι hA J0 lam0 eC
  exact mjFull_of_fullLat T j w A ι hA (fullLat_of_kappa H T hT hj hw) J0 lam0 eC

theorem mLat_of_fullLattice (H : IntegralCuspFormsFullLattice) : MLat :=
  MLat.of_anyLevel (mLatAnyLevel_of_fullLattice H)

end GlobalTheory.GoodLat.Road
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkIffOfRel
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.Pair

theorem inv_form_of_rel {S : Type*} [Ring S] [Algebra ℚ S] (b b' y : Sˣ) (z : S) (s : ℚ)
    (h : (b' : S) = algebraMap ℚ S s * (y * b * z)) :
    s • (z * ((b'⁻¹ : Sˣ) : S) * y) = ((b⁻¹ : Sˣ) : S) := by
  have h1 : algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S) = 1 := by rw [← h, Units.mul_inv]
  calc s • (z * ((b'⁻¹ : Sˣ) : S) * y)
      = ((b⁻¹ : Sˣ) : S) * ((y⁻¹ : Sˣ) : S) * (algebraMap ℚ S s * (y * b * z) * ((b'⁻¹ : Sˣ) : S)) * y := by
        simp only [← Algebra.smul_def, mul_smul_comm, smul_mul_assoc, mul_assoc, Units.inv_mul_cancel_left]
    _ = _ := by rw [h1, mul_one, mul_assoc, Units.inv_mul, mul_one]

theorem form_of_rel {p : ℕ} [Fact p.Prime] {G : HTGroup p} (b b' y : G.Cˣ) (s : ℚ)
    (h : (b' : G.C) = algebraMap ℚ G.C s * (y * b * sh G y)) (v : InfinitePlace G.F) (x : Fin G.n → ℂ) :
    (star x ⬝ᵥ ((G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C)) *ᵥ x)).re =
      (s : ℝ) * (star (G.psi v y *ᵥ x) ⬝ᵥ
        ((G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) *ᵥ (G.psi v y *ᵥ x))).re := by
  have hu : IsUnit (G.gram v).det := (G.gram_det v).isUnit
  have e : G.gram v * G.psi v ((b⁻¹ : G.Cˣ) : G.C) =
      (s : ℂ) • ((G.psi v y)ᴴ * (G.gram v * G.psi v ((b'⁻¹ : G.Cˣ) : G.C)) * G.psi v y) := by
    rw [← inv_form_of_rel b b' y _ s h, map_rat_smul, map_mul, map_mul, sh, G.psi_star, Matrix.mul_smul,
      ← Rat.cast_smul_eq_qsmul ℂ]
    simp only [Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hu]
  rw [e, Matrix.smul_mulVec, dotProduct_smul, Matrix.star_mulVec, ← Matrix.dotProduct_mulVec,
    Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, smul_eq_mul, ← Complex.ofReal_ratCast, Complex.re_ofReal_mul]

theorem mark_iff_of_rel : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P Q : Pair G) (μ : ℂ),
    P.Rel Q → (P.Mark μ ↔ Q.Mark μ) := by
  rintro p _ G P Q μ ⟨y, s, hs, hβ, hγ⟩
  have hs' : (0 : ℝ) < s := by exact_mod_cast hs
  constructor
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v y *ᵥ x, ?_, ?_⟩
    · rw [Matrix.mulVec_mulVec, ← map_mul, hγ, ← Units.val_mul, inv_mul_cancel_right, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ] at hpos
      exact (mul_pos_iff_of_pos_left hs').1 hpos
  · rintro ⟨v, hv, x, hx, hpos⟩
    refine ⟨v, hv, G.psi v ((y⁻¹ : G.Cˣ) : G.C) *ᵥ x, ?_, ?_⟩
    · have e : P.γ * y⁻¹ = y⁻¹ * Q.γ := by rw [hγ]; group
      rw [Matrix.mulVec_mulVec, ← map_mul, ← Units.val_mul, e, Units.val_mul, map_mul,
        ← Matrix.mulVec_mulVec, hx, Matrix.mulVec_smul]
    · rw [form_of_rel P.β Q.β y s hβ, Matrix.mulVec_mulVec x (G.psi v y), ← map_mul, Units.mul_inv, map_one,
        Matrix.one_mulVec]
      exact mul_pos hs' hpos

end GlobalTheory.LKMid.Pair
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MarkedRootRealSignatureOne
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid

theorem eval_eq_zero_of_eigenvector {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (x : Fin n → ℂ) (μ : ℂ) (hx : x ≠ 0)
    (hM : M *ᵥ x = μ • x) (q : Polynomial ℂ) (hq : Polynomial.aeval M q = 0) : q.eval μ = 0 := by
  have hv : Module.End.HasEigenvector (Matrix.toLin' M) μ x :=
    ⟨Module.End.mem_eigenspace_iff.2 (by rw [Matrix.toLin'_apply]; exact hM), hx⟩
  have h1 := Module.End.aeval_apply_of_hasEigenvector hv (p := q)
  have h2 : Polynomial.aeval (Matrix.toLin' M) q = Matrix.toLin' (Polynomial.aeval M q) := by
    exact Polynomial.aeval_algHom_apply (Matrix.toLinAlgEquiv' (R := ℂ) (n := Fin n)).toAlgHom M q
  rw [h2, hq, map_zero, LinearMap.zero_apply] at h1
  exact (smul_eq_zero.1 h1.symm).resolve_right hx

theorem mark_isRoot_pol : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ v : InfinitePlace G.F, sigPosH (G.gram_herm v) = 1 → P.pol.eval₂ v.embedding μ = 0 := by
  intro p _ G P μ ha hm v hv
  obtain ⟨v₀, hv₀, x, hx, hpos⟩ := hm
  have hvv : v = v₀ := by
    unfold HTGroup.a at ha
    obtain ⟨w, hw⟩ := Fintype.card_eq_one_iff.1 ha
    have e1 := hw ⟨v, hv⟩
    have e2 := hw ⟨v₀, hv₀⟩
    exact congrArg Subtype.val (e1.trans e2.symm)
  subst hvv
  have hx0 : x ≠ 0 := by
    rintro rfl
    simp at hpos
  have hq : Polynomial.aeval (G.psi v (P.γ : G.C)) (P.pol.map v.embedding) = 0 := by
    have h0 : G.psi v (Polynomial.aeval (P.γ : G.C) P.pol) = 0 := by
      rw [Pair.pol, minpoly.aeval, map_zero]
    rw [Polynomial.aeval_def, Polynomial.eval₂_map]
    rw [Polynomial.aeval_def, Polynomial.hom_eval₂] at h0
    have e : (algebraMap ℂ (Matrix (Fin G.n) (Fin G.n) ℂ)).comp v.embedding = (G.psi v).comp (algebraMap G.F G.C) := by
      apply RingHom.ext
      intro a
      simp only [RingHom.comp_apply, G.psi_F, Matrix.algebraMap_eq_diagonal, Matrix.scalar_apply]
      rfl
    rw [e]
    exact h0
  have := eval_eq_zero_of_eigenvector _ x μ hx0 hx _ hq
  rwa [Polynomial.eval_map] at this

end GlobalTheory.LKMid
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MassMulVolumeCommensurableStatement
section
open GlobalTheory.LKCount
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mass_mul_volume_commensurable : ∀ {G : Type} [Group G] (Γ' T C C' : Subgroup G), C ≤ T → C' ≤ T → C.relIndex C' ≠ 0 → C'.relIndex C ≠ 0 → (∀ t ∈ T, ((Γ' ⊓ C.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → (∀ t ∈ T, ((Γ' ⊓ C'.map (MulAut.conj t).toMonoidHom : Subgroup G) : Set G).Finite) → massC Γ' T C' * vol C C' = massC Γ' T C := by
  first | exact @GlobalTheory.LKCount.MassChange.massC_mul_vol | exact GlobalTheory.LKCount.MassChange.massC_mul_vol | (intros; apply GlobalTheory.LKCount.MassChange.massC_mul_vol <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemClosureRationalPointsUnitaryGroupStatement
section
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.Published
open scoped TensorProduct
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_closure_rational_points_unitary_group : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → ∀ (T₁ : Finset (InfinitePlace F)) (T₂ : Finset (HeightOneSpectrum (𝓞 F))) (η : AF F), IsPlacesIdem T₁ T₂ η → ∀ h ∈ SUSupp σ J η, h ∈ closure {x : HA (AF F) σ J | ∃ γ ∈ SURat σ J, (∀ i j, ((HA.mat (AF F) σ J x).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j = (1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) i j + algebraMap (AF F) (AF F ⊗[F] E) η * (((HA.mat (AF F) σ J γ).1 : Matrix (Fin M) (Fin M) (AF F ⊗[F] E)) - 1) i j)} := by
  first | exact @GlobalTheory.SUWeakApprox.weak_approx_SU | exact GlobalTheory.SUWeakApprox.weak_approx_SU | (intros; apply GlobalTheory.SUWeakApprox.weak_approx_SU <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemGroupOfCongruent
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Pj Formalism.IndefR.FWT Formalism.IndefR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.PrincCore

set_option maxHeartbeats 1000000 in

theorem mem_group_of_congruent : ∀ (D : D7) (T : Core D), LawsM T → ∀ j, InR D j → ∀ σ, GoodEmb T.Q.c σ → ∀ k (γ : GL (Fin D.R.r) D.host.E), ReciprocityTheory.ChartRestriction.G.FD.IsUStab ((T.U j σ).X k).Gm ((T.U j σ).X k).Λ γ → (∀ v ∈ ((T.U j σ).X k).Λ, ∃ u ∈ ((T.U j σ).X k).Λ, Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) v = v + T.Q.l.M • u) → γ ∈ ((T.U j σ).X k).Γ := by
  intro D T h j hj σ hσ k γ hγ hc0
  have hc : ∀ x ∈ ((T.U j σ).X k).Λ, ∃ y ∈ ((T.U j σ).X k).Λ,
      Matrix.mulVec (γ : Matrix (Fin D.R.r) (Fin D.R.r) D.host.E) x - x = (T.Q.l.M : D.host.E) • y := by
    intro x hx
    obtain ⟨y, hy, e⟩ := hc0 x hx
    exact ⟨y, hy, by rw [e, add_sub_cancel_left, Nat.cast_smul_eq_nsmul]⟩
  obtain ⟨hgood, hA, -, -, -, -, hnum⟩ := GlobalTheory.PinNum.numerics_of_pins D T.Q h.pins
  have hr : 0 < D.R.r := (hnum j hj).2.1
  have hM : 3 ≤ T.Q.l.M := le_trans (hgood 2 Nat.prime_two) (Nat.div_le_self _ _)
  obtain ⟨γ', hγ', u, n, hn, hu, he⟩ := GlobalTheory.unf_group_contains_congruence_upto_rootsOfUnity _ _ _ _ _ _ σ _
    (Formalism.L2.PjFree.Unf.ofPj (T.U j σ)) (h.unf j hj σ hσ) hA hr k γ hγ hc
  obtain ⟨th, hrk, hth, hD⟩ := h.dictU j hj σ hσ
  have hK := h.levelK j hj σ hσ
  rw [← h.pins.2.1.1] at hK
  have h1 := root_eq_one (T.V j σ) hrk hr (T.U j σ).X (T.dict j σ) (T.mu j σ) (T.Kf j σ) th hth hD
    (h.muUnit j hj σ hσ) _ hM hK k γ γ' hγ' hc u n hn hu he
  rw [h1, one_smul] at he
  exact Units.ext he ▸ hγ'

end GlobalTheory.PrincCore
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSubringOfPthPowerTwistedMonomialMem
section
open GlobalTheory GlobalTheory.LogDR

namespace GlobalTheory

theorem LogDR.round_coeff_mem : ∀ (K : Type) [Field K] (p : ℕ) (A : Subring K) (n : ℕ) (x : Fin n → Kˣ) (I J : Finset (Fin n)) (t : Kˣ) (r : Fin n → ℕ) (g : K), 0 < p → AlgChart A x → (∀ j, r j < p) → g ^ p * ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) / ∏ j ∈ I \ J, (x j : K) ∈ A → g * t / ∏ j ∈ I \ J, (x j : K) ∈ A := by
  intro K _ p A n x I J t r g hp hA hr h
  have hP0 : (∏ j ∈ I \ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hQ0 : (∏ j ∈ J, (x j : K)) ≠ 0 := Finset.prod_ne_zero_iff.mpr (fun j _ => (x j).ne_zero)
  have hcast : ((t ^ p * ∏ j ∈ J, x j ^ r j : Kˣ) : K) = (t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j) := by
    push_cast; rfl
  rw [hcast] at h
  have hpow : ∀ j ∈ J, (x j : K) ^ p = (x j : K) ^ (r j) * (x j : K) * (x j : K) ^ (p - 1 - r j) := by
    intro j _
    rw [← pow_succ, ← pow_add]
    congr 1
    have := hr j
    omega
  have hprod : (∏ j ∈ J, (x j : K)) ^ p = (∏ j ∈ J, (x j : K) ^ (r j)) * (∏ j ∈ J, (x j : K)) *
      ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [← Finset.prod_pow, ← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    exact Finset.prod_congr rfl hpow
  have hS : ∏ j ∈ J ∪ I \ J, (x j : K) = (∏ j ∈ J, (x j : K)) * ∏ j ∈ I \ J, (x j : K) :=
    Finset.prod_union Finset.disjoint_sdiff
  have hB : ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) ∈ A :=
    Subring.prod_mem _ (fun j _ => Subring.pow_mem _ (hA.mem j) _)
  have key : (g * t * ∏ j ∈ J, (x j : K)) ^ p / ∏ j ∈ J ∪ I \ J, (x j : K) =
      (g ^ p * ((t : K) ^ p * ∏ j ∈ J, (x j : K) ^ (r j)) / ∏ j ∈ I \ J, (x j : K)) *
        ∏ j ∈ J, (x j : K) ^ (p - 1 - r j) := by
    rw [hS, mul_pow, mul_pow, hprod]
    field_simp
  have h2 := hA.root (J ∪ I \ J) _ p hp (key ▸ A.mul_mem h hB)
  have e : (g * t * ∏ j ∈ J, (x j : K)) / ∏ j ∈ J ∪ I \ J, (x j : K) = g * t / ∏ j ∈ I \ J, (x j : K) := by
    rw [hS]
    field_simp
  rwa [e] at h2

end GlobalTheory
end

