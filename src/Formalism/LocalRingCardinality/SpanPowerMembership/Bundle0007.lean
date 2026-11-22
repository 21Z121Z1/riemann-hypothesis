import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators
import Formalism.LocalRingCardinality.SpanPowerMembership.Places
import Formalism.LocalRingCardinality.SpanPowerMembership.Adelic
import Formalism.LocalRingCardinality.SpanPowerMembership.Spaces
import Formalism.LocalRingCardinality.SpanPowerMembership.Bundle0006
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleWeightMiddleEntries
import Formalism.LocalRingCardinality.SpanPowerMembership.FmZeroHLatEmpty
import Formalism.LocalRingCardinality.SpanPowerMembership.PlacesOverNcardOfSplitInj
import Formalism.LocalRingCardinality.SpanPowerMembership.GPlacesExampleNatAct
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleNewtypesIdempotentZero
import Formalism.LocalRingCardinality.SpanPowerMembership.LocAtB
import Formalism.LocalRingCardinality.SpanPowerMembership.HaarDensityNeZero
import Formalism.SharpRestriction.InertJacobiLevels.Bundle0001

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.ExampleClassGroupCardPos
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂

open NumberField IsDedekindDomain

structure LocalGap {R : Ranks} (H : Host R) where

  nloc : LocTheory

  nlocA : ∀ (l : ℕ) [Fact l.Prime], LocAinf l (nloc l)

  nlocT : ∀ (l : ℕ) [Fact l.Prime], LocTied l (nloc l) (nlocA l)

theorem LocalGap.tame {R : Ranks} {H : Host R} (_G : LocalGap H) : TameHyp H := tameHyp H

def LocalGap.cd {R : Ranks} {H : Host R} (_G : LocalGap H) : CDHaar := CD.cdHaar

def LocalGap.transport {R R' : Ranks} {H : Host R} (G : LocalGap H) (H' : Host R') : LocalGap H' :=
  ⟨G.nloc, G.nlocA, G.nlocT⟩

def LocalGap.localGapOfRecord (D : D7) {R : Ranks} (H : Host R) : LocalGap H := ⟨D.loc, D.locA, D.locT⟩

variable (H : Host R0) (T : ℕ) [hT : Fact T.Prime]

abbrev Tau0 : Type := ↥(R0.Psi)

theorem exampleClassGroupCard_pos {R : Ranks} (H : Host R) : 0 < exampleClassGroupCard H := by
  unfold exampleClassGroupCard
  refine Finset.prod_pos (fun k _ => pow_pos ?_ _)
  have : NeZero (H.g k) := ⟨(H.g_prime k).ne_zero⟩
  exact Nat.card_pos

abbrev rowsH : Rows.Data R0 :=
  toyRowsOfNumberField H.E H.φ₀ (@placesOf H.E _ _ H.cmStar) Tau0 card_examplePsi_eq (dstarOf T) (shaExample H)
    (shaExample_nonneg H) (exampleClassGroupCard H) (exampleClassGroupCard_pos H)

abbrev memT : Member R0 Tau0 (fun _ => hc0) := trivialMember Tau0 T (dstarOf T) (dstarOf_pos T)

theorem nHypH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) :
    NHyp H (rowsH H T) where
  hsha := fun p _ e _ _ => shaExample_eq H p e
  hcard := rfl
  hg := hg

theorem normAt_empty {K V ι : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
    [Fintype ι] [DecidableEq ι] [IsEmpty ι] (b : Module.Basis ι K V)
    (X : InfinitePlace K → Matrix ι ι ℂ) (v : InfinitePlace K) (x : V) :
    Formalism.HermitianLatticesTheory.normAt b X v x = 0 := by
  simp [Formalism.HermitianLatticesTheory.normAt, Formalism.HermitianLatticesTheory.cnorm]

def spH (pz : H.E) (hpz : pz * H.conj pz = (T : H.E)) :
    @Spaces R0 H.F H.E _ _ _ _ H.cmStar _ :=
  letI := H.cmStar
  spacesExample star_isIntegral (cmData H) T hT.out pz
    (by rw [star_eq_conj H pz, mul_comm]; exact hpz)
    (exists_adelic_neg_one H (cmData H).sig (fun x => star_eq_conj H x))

abbrev sDataH (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H) :
    Formalism.MainNotions.S.Draft.SData R0 H.F H.E (conjF H) Unit Tau0 (fun _ _ => hc0) :=
  toySData (conjF H) (fun _ _ => hc0) 1 one_pos (fun _ _ l h => exampleWeight_cloud_gap_four l h)
    (fun _ _ l h => exampleWeight_middle_entries l h) (locAdj (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some))

set_option synthInstance.maxHeartbeats 200000 in
set_option maxHeartbeats 1600000 in

def exampleRecordOfData
    (hg : ∀ k, (placesOver H.E (H.g k)).ncard = Module.finrank ℚ H.E) (ht : THyp H)
    (hlev : T ∈ H.levelPrimes) (hpde : T ≠ H.pde ∧ T ≠ H.pde')
    (pz : 𝓞 H.E) (hK : (pz : H.E) ∈ H.K) (hpz : (pz : H.E) * H.conj (pz : H.E) = (T : H.E))
    (hcong : (pz - 1) ∈ Ideal.span {((H.QS * H.q * H.d * (H.g 0 * H.g 1) ^ 2 : ℕ) : 𝓞 H.E)})
    (G : LocalGap H) : D7 :=
  letI : StarRing H.E := H.cmStar
  { R := R0
    host := H
    sp := spH H T pz hpz
    what₂ := rowsH H T
    eTau := Equiv.refl _
    hc := fun _ => hc0
    wordFin := inferInstanceAs (Fintype Unit)
    u₀ := ()
    hcW := fun _ _ => hc0
    hcW_base := rfl
    hcW_v := fun _ _ => rfl
    hcW_b := fun _ _ => rfl
    hcW_e := fun _ _ => rfl
    hcW_first := fun _ _ _ => rfl
    hcW_last := fun _ _ _ => rfl
    mem := fun _ => memT T
    nfLL := inferInstanceAs (NumberField H.E)
    starLL := H.cmStar
    tcLL := instTotallyComplex H
    galLL := instIsGalois H
    starLL_cx := fun x => emb_star H H.φ₀ x
    div := toyZeroLatticeDatum H.E
    div_good := ⟨(zeroHLat_good H.E).1, fun _ => (zeroHLat_good H.E).1⟩
    embE := RingHom.id _
    embE_φ₀ := rfl
    conjF := conjF H
    conjF_eq := conjF_apply H
    embE_conj := fun x => (star_eq_conj H x).symm
    LL0 := ⊤
    hostField_le_fixedField := fun _ => IntermediateField.mem_top
    O_contains := fun x => ⟨x, rfl⟩
    plEq := Equiv.refl _
    val_eq := placesOf_val_eq H.E
    ram_eq := placesOf_ram_eq H.E
    conj_val := placesOf_conj_val H.E
    T_level := fun _ => hlev
    T_norm := fun _ => ⟨pz, hK, hpz, hcong⟩
    sp_T := rfl
    cOf := fun _ => 1
    cOf_ne := fun _ => one_ne_zero
    cOf_eq := fun _ => by rw [map_one, one_mul, one_mul]
    T_win := fun _ => exampleLevel_near_lower Tau0 T
    GamP_eq := fun _ => rfl
    T_ne_pde := fun _ => hpde
    Dstar_eq := fun _ => rfl
    clsLat := fun _ _ c => Empty.elim c
    clsLat_lat := fun _ _ c => Empty.elim c
    eMu := fun _ => toyZeroSpaceEquiv Tau0 T (dstarOf T) (dstarOf_pos T)
    eMt := fun _ => toyZeroSpaceRefl
    perCol_base_eq_PtilCol := fun _ _ _ => rfl
    Bu_linL := fun _ _ => zero_isLinear
    Bu_linR := fun _ _ => zero_isLinear
    chTw := fun _ _ => (memT T).C
    memberColumns_twistedChain_base := fun _ => rfl
    e0Tw := fun _ _ => LinearEquiv.refl ℂ _
    PTw := fun _ _ => (memT T).P
    eMtTw := fun _ _ => toyZeroSpaceRefl
    perCol_tie := fun _ _ h => absurd rfl h
    vol := fun _ => 1
    vol_pos := fun _ => one_pos
    O_int := fun y => RingOfIntegers.isIntegral_coe y
    jEE := jZero H.E H.φ₀
    jEE_basis := jZero_basis H.E H.φ₀
    jN := fun _ => jZero H.E H.φ₀
    jN_basis := fun _ => jZero_basis H.E H.φ₀
    Dall_eq := rfl
    delP_eq := rfl
    Dt := ℂˣ
    detCls := fun _ _ _ => 1
    muTil := fun _ => 1
    chiD := MonoidHom.id _
    UO := ⊥
    chiD_UO := fun _ hx => Subgroup.mem_bot.mp hx
    e1Dt := exampleInverseEmbeddingProduct H (Equiv.refl Tau0)
    rest_detCharacter_on_unitary_eq := exampleCharacter_unitary_product H (Equiv.refl Tau0)
    relDet := fun N L L' => QuotientGroup.mk (relDetExample H (Equiv.refl Tau0) N L L')
    relDet_self := fun N L => by rw [relDetExample_self]; rfl
    relDet_mul := fun N L L' L'' => by rw [← QuotientGroup.mk_mul, relDetExample_mul]
    relDet_smul := fun N L L' γ h => congrArg _ (relDetExample_smul H (Equiv.refl Tau0) N L L' γ h)
    rhoDet_eq_inv_muTilde_chiD_pow := fun _ _ c => Empty.elim c
    rhoDetPrime_eq_muTilde_mul_chi_pow := fun _ i c => Empty.elim c
    dsig := toyConstantOne _
    dsig_pos := toyConstantOne_pos _
    s := sDataH H hg ht
    s_split := locAdj_split (conjF H) {H.g 0, H.g 1} (slocH H)
      (fun p hp => (splH H hg ht.jac p hp).some)
    s_HH := toySData_HH _ _ _ _ _
    s_Cu := fun u => toySData_Cu _ _ _ _ _ u _ rfl
    s_PlF := toySData_PlF _ _ _ _ _
    loc := G.nloc
    locA := G.nlocA
    locT := G.nlocT
    nd := ndToy H (rowsH H T) (nHypH H T hg)
    ntw := ntwToy H ⊤ (nHypH H T hg)
    naut := nautToy H (rowsH H T) (nHypH H T hg)
    nbc := nbcToy H (rowsH H T) (nHypH H T hg)
    nexp := nexpToy H ⊤ (nHypH H T hg)
    ntypes := ntypesT H (rowsH H T) (nHypH H T hg) ht G.tame
    nStage_trivialCharacter_compat := @ntypesT_E0Tie _ H (rowsH H T) (nHypH H T hg)
      (fun _ => inferInstanceAs (Subsingleton Z0)) (fun _ _ => inferInstanceAs (Subsingleton Z0)) ht G.tame
    nth := nthToy H ⊤ (nHypH H T hg)
    nbr := fun i => Empty.elim i
    self_good := fun i => Empty.elim i
    ntwbr := fun i => Empty.elim i
    nbr_ind := fun i => Empty.elim i
    ntwbr_ind := fun i => Empty.elim i
    loc_tie := fun i => Empty.elim i
    bc_tie := fun i => Empty.elim i
    rbar_tie := fun i => Empty.elim i
    mtpar_tie := fun i => Empty.elim i
    jetW := fun i => Empty.elim i
    jetW_l := fun i => Empty.elim i
    jetTau := fun i => Empty.elim i
    jetW1 := fun i => Empty.elim i
    resChar_thetaJetPlaceDegOne := fun i => Empty.elim i
    jetTau1 := fun i => Empty.elim i
    nStage_trivialCharacter_coeff_eq := fun g => (map_zero H.φ₀).trans (newtypes_idempotent_zero H _ _ ht G.tame g).symm
    Z_tie := example_Z_compatibility H _ _
    Zgood_tie := example_goodZ_compatibility H _ _
    etaJ_tie := example_etaJ_compatibility H _ _ (fun _ _ => rfl)
    fm := fun _ => formsToy H.φ₀ (placesOf H.E) card_examplePsi_eq (memT T).C (memT T).A (memT T).P
    eMu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim φ 0, inner_zero_left]
      exact (Finset.sum_of_isEmpty _).symm
    nuIn := fun _ => 0
    nuIn_inj := fun _ x y _ => Subsingleton.elim (α := Fin 0 → H.E) x y
    nuIn_range := fun _ => Subsingleton.elim (α := Submodule H.E (Fin 0 → H.E)) _ _
    nuIn_jN := fun _ _ => funext fun c => Empty.elim c
    nuIn_norm := fun _ v x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (normAt_empty (ι := Fin 0) _ _ _ _).symm
    jEE_norm := fun x => by
      exact (normAt_empty (ι := Fin 0) _ _ _ _).trans (norm_zero (E := Z0)).symm
    sEE := ⟨0, fun x => (norm_zero (E := Z0)).trans
      ((norm_zero (E := Z0)).symm.trans (congrArg norm (Subsingleton.elim (α := Z0) 0 x)))⟩
    s_Cu_isom := fun _ φ ψ => by
      rw [Subsingleton.elim (α := Z0) φ 0]
      exact (inner_zero_left (𝕜 := ℂ) (E := Z0) ψ).trans (Finset.sum_of_isEmpty _).symm
    cd := G.cd
    jet := jetToy R0 H
    jetU := fun i => Empty.elim i
    jetL := fun i => Empty.elim i
    jetL' := fun i => Empty.elim i
    jetU1 := fun i => Empty.elim i
    jetL1 := fun i => Empty.elim i
    jetL1' := fun i => Empty.elim i
    gx := gxExample _ _
    gat := fun _ _ _ => gAtPExample _
    gat_d := fun _ _ _ => (gAtPExample_d _).trans (finrank_bot ℂ _).symm
    Y_sigval := spacesExample_Ysig _ _ _ _ _ _ _ }

end Formalism.BasicNotions.Examples₂
end
end

-- bundled from Formalism.LocalRingCardinality.SpanPowerMembership.ThetaFullColIsom
section
noncomputable section

namespace Formalism.BasicNotions.Examples₂.NZ

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.Inhab NumberField

attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] Classical.propDecidable

section Conj

variable (V : Type) [AddCommGroup V] [Module ℂ V]

def cj (v : V) : V :=
  (Module.Basis.ofVectorSpace ℂ V).repr.symm
    (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _))

theorem cj_add (v w : V) : cj V (v + w) = cj V v + cj V w := by
  unfold cj
  rw [map_add, Finsupp.mapRange_add (fun a b => map_add (starRingEnd ℂ) a b), map_add]

theorem cj_smul (c : ℂ) (v : V) : cj V (c • v) = star c • cj V v := by
  unfold cj
  have : (c • (Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) =
      star c • ((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _) := by
    ext i
    simp
  rw [LinearEquiv.map_smul (Module.Basis.ofVectorSpace ℂ V).repr c v, this, LinearEquiv.map_smul]

theorem cj_cj (v : V) : cj V (cj V v) = v := by
  unfold cj
  rw [LinearEquiv.apply_symm_apply]
  have : (((Module.Basis.ofVectorSpace ℂ V).repr v).mapRange (starRingEnd ℂ) (map_zero _)).mapRange
      (starRingEnd ℂ) (map_zero _) = (Module.Basis.ofVectorSpace ℂ V).repr v := by
    ext i
    simp
  rw [this, LinearEquiv.symm_apply_apply]

end Conj

variable (D : D7)

abbrev HR : Type := lp (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2

abbrev HC : Type := lp (fun u : D.what₂.Word => D.what₂.Mu u) 2

abbrev HF : Type := HR D × HC D

def petH (a b : HF D) : ℂ := inner ℂ a.1 b.1 + inner ℂ a.2 b.2

def rowI (μ : D.what₂.Tup) (j : ℕ) : D.what₂.Mult μ j →ₗ[ℂ] HF D :=
  (LinearMap.inl ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩)

def rowP (μ : D.what₂.Tup) (j : ℕ) : HF D →ₗ[ℂ] D.what₂.Mult μ j :=
  (lp.evalₗ (𝕜 := ℂ) (fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩).comp
    (LinearMap.fst ℂ (HR D) (HC D))

def colI (u : D.what₂.Word) : D.what₂.Mu u →ₗ[ℂ] HF D :=
  (LinearMap.inr ℂ (HR D) (HC D)).comp
    (lp.lsingle (𝕜 := ℂ) (E := fun u : D.what₂.Word => D.what₂.Mu u) 2 u)

theorem component_inclusion (μ j) (x : D.what₂.Mult μ j) : rowP D μ j (rowI D μ j x) = x :=
  lp.single_apply_self (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x

theorem pet_rowI (μ j) (x : D.what₂.Mult μ j) (b : HF D) : petH D (rowI D μ j x) b = inner ℂ x (rowP D μ j b) := by
  show inner ℂ (lp.single (E := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) 2 ⟨μ, j⟩ x) b.1 +
    inner ℂ (0 : HC D) b.2 = _
  rw [inner_zero_left, add_zero]
  exact lp.inner_single_left (G := fun i : (Σ _ : D.what₂.Tup, ℕ) => D.what₂.Mult i.1 i.2) ⟨μ, j⟩ x b.1

theorem pet_colI (u) (x y : D.what₂.Mu u) : petH D (colI D u x) (colI D u y) = inner ℂ x y := by
  show inner ℂ (0 : HR D) 0 + inner ℂ (lp.single 2 u x) (lp.single 2 u y) = _
  rw [inner_zero_left, zero_add, lp.inner_single_left (G := fun u : D.what₂.Word => D.what₂.Mu u) u x]
  rw [lp.single_apply_self]

def toTop {M : Type} [AddCommGroup M] [Module ℂ M] (f : M →ₗ[ℂ] HF D) : M →ₗ[ℂ] (⊤ : Submodule ℂ (HF D)) :=
  f.codRestrict ⊤ fun _ => Submodule.mem_top

def thetaFull : ThetaX D where
  AF := fun _ => HF D
  cusp := fun _ => ⊤
  pet := fun _ F G => petH D F G
  pet_add_left := fun _ F F' G => by
    simp only [petH, Prod.fst_add, Prod.snd_add, inner_add_left]; ring
  pet_smul_left := fun _ c F G => by
    simp only [petH, Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_add]; rfl
  pet_right := fun _ F => ⟨fun G G' => by
      simp only [petH, Submodule.coe_add, Prod.fst_add, Prod.snd_add, inner_add_right]; ring,
    fun c G => by
      simp only [petH, Submodule.coe_smul, Prod.smul_fst, Prod.smul_snd, inner_smul_right, smul_eq_mul, mul_add]⟩
  pet_symm := fun _ F G => by
    simp only [petH, star_add]
    rw [← starRingEnd_apply, ← starRingEnd_apply, inner_conj_symm, inner_conj_symm]
  pet_pos := fun _ F hF => by
    have h1 : (F : HF D) ≠ 0 := fun h => hF (Subtype.ext h)
    have e : (petH D (F : HF D) F).re = ‖(F : HF D).1‖ ^ 2 + ‖(F : HF D).2‖ ^ 2 := by
      simp only [petH, Complex.add_re]
      rw [← inner_self_eq_norm_sq (𝕜 := ℂ), ← inner_self_eq_norm_sq (𝕜 := ℂ)]; rfl
    show 0 < (petH D (F : HF D) F).re
    rw [e]
    rcases (not_and_or.mp fun h : (F : HF D).1 = 0 ∧ (F : HF D).2 = 0 => h1 (Prod.ext h.1 h.2)) with h | h
    · have := norm_pos_iff.mpr h; positivity
    · have := norm_pos_iff.mpr h; positivity
  actR := fun _ _ _ => 1
  actR_one := fun _ _ => rfl
  actR_mul := fun _ _ _ _ _ _ => (one_mul _).symm
  actR_cusp := fun _ _ _ _ _ _ => Submodule.mem_top
  Gf := fun _ => PUnit
  actF := fun _ => 1
  actF_cusp := fun _ _ _ _ => Submodule.mem_top
  actF_actR := fun _ _ _ _ => rfl
  Ksph := fun _ _ => ⊤
  Ksph_mono := fun _ _ _ _ => le_refl _
  typ := fun _ _ => ⊤
  Chr := Multiplicative (D.what₂.Tau → ℚ)
  infTy := fun χ τ => Multiplicative.toAdd χ τ
  infTy_mul := fun _ _ _ => rfl
  chrOf := fun _ j => Multiplicative.ofAdd (chrExp D j)
  chrOf_inf := fun _ j τ => by
    show chrExp D (j.1 + 1) τ = _
    unfold chrExp
    rw [dif_pos ⟨Nat.le_add_left _ _, j.2⟩]
    rfl
  etaT := Multiplicative.ofAdd fun _ => 1 / 2
  etaT_inf := fun _ => Or.inl rfl
  etaT_pos := fun _ => rfl
  Sch := fun _ _ => HF D →ₗ[ℂ] HF D
  fact := fun _ _ => Set.univ
  kfin := fun _ _ => ⊤
  th := fun _ _ _ _ => LinearMap.lcomp ℂ (HF D) (⊤ : Submodule ℂ (HF D)).subtype
  Xs := fun t => (tow D t).Xs
  Xs_rank := fun t => (tow D t).Xs_rank
  Xs_sig := fun t => (tow D t).Xs_sig
  Ys := fun t => (tow D t).Ys
  Ys_rank := fun t => (tow D t).Ys_rank
  Ys_sig := fun t => (tow D t).Ys_sig
  iXYs := fun t => (tow D t).iXYs
  iXYs_isom := fun t => (tow D t).iXYs_isom
  iYXm := fun t => (tow D t).iYXm
  iYXm_isom := fun t => (tow D t).iYXm_isom
  YsLow := fun t j _ => (tow D t).Ys j
  YsLow_zero := fun _ _ => rfl
  Xs_rec := fun j _ => by rw [tow_rec]; rfl
  Ys_rec := fun j _ => by rw [tow_rec]; rfl
  conjAF := fun _ => cj (HF D)
  conjAF_add := fun _ => cj_add _
  conjAF_smul := fun _ => cj_smul _
  conjAF_conjAF := fun _ => cj_cj _
  conjAF_cusp := fun _ _ _ => Submodule.mem_top
  Pos := fun _ _ _ => PUnit
  FJd := fun _ _ _ => PUnit
  Bper := fun _ _ _ _ _ _ _ => 0
  Bper_right := fun _ _ _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Bper_add_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_smul_left := fun _ _ _ _ _ _ _ _ => by simp
  Bper_odd := fun _ _ _ _ _ _ _ _ _ => rfl
  Btop := fun _ _ _ _ _ => 0
  Btop_right := fun _ _ _ _ => ⟨fun _ _ => by simp, fun _ _ => by simp⟩
  Btop_add_left := fun _ _ _ _ _ _ => by simp
  Btop_smul_left := fun _ _ _ _ _ _ => by simp
  pos1 := fun _ => PUnit.unit
  posSym := fun _ => PUnit.unit
  colAF := fun u _ _ => toTop D (colI D u)
  rowAF := fun μ j => toTop D (rowI D μ j)
  PhiY := fun μ j => (rowI D μ j).comp ((D.what₂.io μ j).comp (rowP D μ (j + 1)))
  PhiYup := fun _ _ => 0
  mY := fun _ _ => 1
  mY_pos := fun _ _ => one_pos
  adelicDataRowMeasureScale_trivialTuple := fun _ => rfl
  mY_zero := fun _ => rfl

theorem thetaFull_mY (μ : D.what₂.Tup) (j : ℕ) : (((thetaFull D).mY μ j : ℝ) : ℂ) = 1 := Complex.ofReal_one

theorem thetaFull_row : (thetaFull D).TieRowIsom := fun μ j _ x y => by
  unfold ThetaX.petY
  rw [thetaFull_mY, one_mul]
  exact (pet_rowI D μ j x (rowI D μ j y)).trans (by rw [component_inclusion])

theorem thetaFull_io : (thetaFull D).TieIo := fun μ j _ y x => by
  unfold ThetaX.petY ThetaX.dnY
  rw [thetaFull_mY, thetaFull_mY, one_mul, one_smul]
  show petH D (rowI D μ j (D.what₂.io μ j (rowP D μ (j + 1) (rowI D μ (j + 1) y)))) (rowI D μ j x) = _
  rw [component_inclusion, pet_rowI, component_inclusion]

theorem thetaFull_colIsom (u μ j) (x y : D.what₂.Mu u) :
    (thetaFull D).pet _ (((thetaFull D).colAF u μ j x : (thetaFull D).cusp _) : (thetaFull D).AF _)
      ((thetaFull D).colAF u μ j y) = inner ℂ x y := pet_colI D u x y

theorem theta_exists : ∃ X : ThetaX D, X.TieRowIsom ∧ X.TieIo :=
  ⟨thetaFull D, thetaFull_row D, thetaFull_io D⟩

end Formalism.BasicNotions.Examples₂.NZ
end
end

