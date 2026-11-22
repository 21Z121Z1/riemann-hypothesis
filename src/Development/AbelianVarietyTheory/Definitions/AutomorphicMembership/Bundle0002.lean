import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.SpreadLe
import Formalism.LocalToGlobal.Columns.AbelianHostFieldConditions
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsMemberFormsNonempty
import Formalism.FrobeniusOrbits.FrobeniusOrbitsProofs.MuCardLeTwo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0013
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CurvNormNonneg

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BaseDataEmbeddingConj
section
namespace GlobalTheory.Mem

open Formalism.BasicNotions NumberField IsDedekindDomain

noncomputable section

open Formalism.L2.Col

@[reducible] def Base.fields (B : Base) : Fields where
  F := B.host.F
  E := B.host.E
  K := B.LL
  starE := B.host.cmStar
  Tau := Tau B.R
  deTau := Classical.decEq _
  emb := B.tauLL

@[reducible] def Base.primes (B : Base) (X : PreX B.toPre) : Primes B.fields where
  cond := B.host.QS * B.host.q * B.host.d
  g := B.host.g
  piG := X.piG
  Word := B.Word
  deWord := Classical.decEq _
  T := B.T
  piT := X.piT

open Classical in

@[reducible] def Base.wts (B : Base) : Wts B.fields B.Word B.R where
  row := fun τ => RowPar.of (B.hc τ)
  hc := B.hcW
  tops := Finset.univ.filter fun τ : Tau B.R => (τ : B.R.GG) ∈ B.host.topPlaces

@[reducible] def Base.dat (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) : Dat where
  R := B.R
  X := B.fields
  sig0 := B.embLL
  Pr := B.primes X
  Ch := Ch
  W := B.wts
  a := X.a

namespace Base

variable (B : Base)

theorem fields_star (x : B.host.E) : letI := B.fields.starE; star x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_sig (x : B.host.E) : B.fields.sig x = B.host.conj x := bridge_star_holds B.R B.host x

theorem fields_emb_apply (τ : Tau B.R) (x : B.host.E) :
    B.fields.emb τ x = B.embE (B.host.sigmaOf (τ : B.R.GG) x) := rfl

theorem fields_f : B.fields.f = B.R.f := card_Tau B.host

theorem fields_embC (τ : Tau B.R) : B.fields.embC B.embLL τ = B.host.emb (τ : B.R.GG) := by
  unfold Fields.embC Host.emb
  rw [← B.embE_φ₀]
  rfl

theorem fields_conjO_coe (x : 𝓞 B.host.E) :
    ((B.fields.conjO x : 𝓞 B.host.E) : B.host.E) = B.host.conj (x : B.host.E) :=
  B.fields_star (x : B.host.E)

theorem primes_piGCong (X : PreX B.toPre) : (B.primes X).PiGCong := X.piG_cong

theorem primes_piG_norm (X : PreX B.toPre) (i : Fin 2) :
    (B.primes X).piG i * B.fields.conjO ((B.primes X).piG i) = ((B.primes X).g i : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piG_norm i
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem primes_piT_norm (X : PreX B.toPre) (u : B.Word) :
    (B.primes X).piT u * B.fields.conjO ((B.primes X).piT u) = ((B.primes X).T u : 𝓞 B.fields.E) := by
  apply RingOfIntegers.coe_injective
  have h := X.piT_norm u
  rw [← B.fields_conjO_coe] at h
  simpa using h

theorem mem_wts_tops (τ : Tau B.R) : τ ∈ B.wts.tops ↔ (τ : B.R.GG) ∈ B.host.topPlaces := by
  classical
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]

theorem wts_isOk : B.wts.Ok where
  row_ok τ := ⟨B.hc τ, rfl⟩
  hc_row u τ := by
    show RowPar.of (B.hcW u τ) = RowPar.of (B.hc τ)
    unfold RowPar.of
    rw [B.hcW_v, B.hcW_b, B.hcW_e]
  u_first u u' τ h := (B.hcW_first u τ h).trans (B.hcW_first u' τ h).symm
  u_last u u' τ h := (B.hcW_last u τ (by omega)).trans (B.hcW_last u' τ (by omega)).symm

theorem primes_sizes (X : PreX B.toPre) : Sizes (B.primes X) B.wts X.a where
  g_big i := by rw [B.fields_f]; exact X.g_big i
  T_gt := X.T_gt
  a_gt := by rw [B.fields_f]; exact X.a_gt
  spread_le u j hj τ := by
    unfold Wts.lamTrue
    rw [spread_shiftW]
    exact X.spread_le u j hj τ

theorem baseData_embedding_conj (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (x : (B.dat X Ch).X.K) :
    (B.dat X Ch).sig0 (star x) = starRingEnd ℂ ((B.dat X Ch).sig0 x) := B.starLL_cx x

theorem dat_e_even (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (j : Fin (B.dat X Ch).R.m) :
    ∃ z : ℤ, ∑ τ, ((B.dat X Ch).W.row τ).e j = 2 * (z : ℚ) := (X.e_even j).even

end Base

example (B : Base) : B.fields.f = 2 * B.R.n := B.fields_f

example (B : Base) (X : PreX B.toPre) (i : Fin 2) : B.host.g i ≡ 1 [MOD B.host.QS * B.host.q * B.host.d] :=
  (B.primes_piGCong X).g_cong (B.primes_piG_norm X) i

example (B : Base) (X : PreX B.toPre) (Ch : Chars B.fields (B.primes X) B.R.m) (u : B.Word) :
    0 < (B.dat X Ch).a ∧ 2 * B.fields.f * B.R.N B.R.m + 1 < B.T u :=
  ⟨(B.primes_sizes X).a_pos, (B.primes_sizes X).T_big u⟩

end

end GlobalTheory.Mem
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsPotential
section
noncomputable section

namespace GlobalTheory.Mem.ColsModel

open Formalism.BasicNotions NumberField IsDedekindDomain

theorem exists_potential {G A X : Type} [Group G] [CommGroup A] (χ : G →* A) (r : G → X → X → Prop)
    (h1 : ∀ x, r 1 x x) (hi : ∀ g x y, r g x y → r g⁻¹ y x)
    (hm : ∀ g g' x y z, r g x y → r g' y z → r (g' * g) x z) (hs : ∀ g x, r g x x → χ g = 1) :
    ∃ φ : X → A, ∀ g x y, r g x y → (φ x)⁻¹ * φ y = χ g := by
  let s : Setoid X := ⟨fun x y => ∃ g, r g x y, fun x => ⟨1, h1 x⟩, fun ⟨g, h⟩ => ⟨_, hi _ _ _ h⟩,
    fun ⟨g, h⟩ ⟨g', h'⟩ => ⟨_, hm _ _ _ _ _ h h'⟩⟩
  have hb : ∀ x, ∃ g, r g (Quotient.mk s x).out x := fun x => Quotient.mk_out (s := s) x
  choose c hc using hb
  refine ⟨fun x => χ (c x), fun g x y h => ?_⟩
  have e : Quotient.mk s x = Quotient.mk s y := Quotient.sound ⟨g, h⟩
  have h2 := hm _ _ _ _ _ (hm _ _ _ _ _ (hc x) h) (hi _ _ _ (hc y))
  rw [← e] at h2
  have h3 := hs _ _ h2
  simp only [map_mul, map_inv] at h3
  rw [inv_mul_eq_one] at h3
  show (χ (c x))⁻¹ * χ (c y) = χ g
  rw [h3, mul_comm (χ g), inv_mul_cancel_left]

theorem isIntegral_det {E : Type} [Field E] [NumberField E] {N : ℕ} (L : Submodule (𝓞 E) (Fin N → E))
    (hfg : L.FG) (hsp : Submodule.span E (L : Set (Fin N → E)) = ⊤) (γ : Matrix (Fin N) (Fin N) E)
    (hγ : ∀ v ∈ L, γ.mulVec v ∈ L) : IsIntegral ℤ γ.det :=
  _root_.GlobalTheory.IsIntegralDetLattice.isIntegral_det_of_preserves_lattice L hfg hsp γ hγ

section Host

variable {R : Ranks} (H : Host R)

def chi : letI := H.cmStar; unitary H.E →* ℂˣ :=
  letI := H.cmStar
  ∏ τ : Tau R, ((Units.map (H.emb ((τ : R.Psi) : R.GG) : H.E →* ℂ)).comp
    Unitary.toUnits)⁻¹

theorem chi_apply : letI := H.cmStar; ∀ z : unitary H.E, ((chi H z : ℂˣ) : ℂ) =
    ∏ τ : Tau R, (H.emb ((τ : R.Psi) : R.GG) (z : H.E))⁻¹ := by
  intro z
  simp [chi]

private theorem prod_sigmaOf (x : H.E) :
    ∏ τ : Tau R, H.sigmaOf ((τ : R.Psi) : R.GG) x = algebraMap H.K H.E (Algebra.norm H.K x) := by
  have := H.galois
  rw [Algebra.norm_eq_prod_automorphisms]
  symm
  have hm : ∀ σ : H.E ≃ₐ[H.K] H.E, H.gal (σ.restrictScalars ℚ) ∈ R.Psi := fun σ =>
    (H.galE_mem_Psi_iff _).2 (σ.commutes ⟨H.sqd, IntermediateField.mem_adjoin_simple_self ℚ _⟩)
  refine Fintype.prod_bijective (fun σ => ⟨_, hm σ⟩) ⟨fun a b h => ?_, fun τ => ?_⟩ _ _ (fun σ => ?_)
  · exact AlgEquiv.restrictScalars_injective ℚ (H.gal.injective (congrArg Subtype.val h))
  · have h1 : H.sigmaOf τ H.sqd = H.sqd := (H.galE_mem_Psi_iff _).1 (by simpa [Host.sigmaOf] using τ.2)
    have h2 : H.sigmaOf τ ∈ H.K.fixingSubgroup := by
      rw [IntermediateField.mem_fixingSubgroup_iff]
      intro y hy
      induction hy using IntermediateField.adjoin_induction with
      | mem y hy => rw [Set.mem_singleton_iff.1 hy]; exact h1
      | algebraMap y => exact AlgEquiv.commutes _ y
      | add y z _ _ hy hz => rw [map_add, hy, hz]
      | inv y _ hy => rw [map_inv₀, hy]
      | mul y z _ _ hy hz => rw [map_mul, hy, hz]
    refine ⟨IntermediateField.fixingSubgroupEquiv H.K ⟨_, h2⟩, Subtype.ext ?_⟩
    exact H.gal.apply_symm_apply _
  · simp [Host.sigmaOf]

theorem chi_of_integral : letI := H.cmStar; ∀ z : unitary H.E, IsIntegral ℤ (z : H.E) → chi H z = 1 := by
  letI := H.cmStar
  intro z hz
  have := H.isCMField_hostE
  obtain ⟨n, hn, hp⟩ := NumberField.Embeddings.pow_eq_one_of_norm_eq_one H.E ℂ hz (fun φ => by
    have h1 : star (z : H.E) * z = 1 := z.2.1
    have h2 : φ (star (z : H.E)) = starRingEnd ℂ (φ z) := IsCMField.complexEmbedding_complexConj H.E φ z
    have h3 := congrArg φ h1
    rw [map_mul, h2, map_one, Complex.conj_mul'] at h3
    have h4 : ‖φ z‖ ^ 2 = 1 := by exact_mod_cast h3
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) two_ne_zero).1 h4)
  apply Units.ext
  rw [chi_apply]
  have h := congrArg H.φ₀ (prod_sigmaOf H (z : H.E))
  rw [H.der.norm_mu z ⟨n, hn, hp⟩, map_one, map_one, map_prod] at h
  rw [Finset.prod_inv_distrib, Units.val_one, inv_eq_one]
  exact h

theorem exists_pot (N : ℕ) : letI := H.cmStar; ∃ φ : SDLat H.E N → ℂˣ,
    ∀ (γ : Matrix.unitaryGroup (Fin N) H.E) (L L' : SDLat H.E N),
      L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1 →
      (φ L)⁻¹ * φ L' = chi H ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩ := by
  letI := H.cmStar
  let dt : Matrix.unitaryGroup (Fin N) H.E →* unitary H.E :=
    { toFun := fun γ => ⟨(γ : Matrix (Fin N) (Fin N) H.E).det, Matrix.det_of_mem_unitary γ.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp) }
  have hone : ∀ L : Submodule (𝓞 H.E) (Fin N → H.E), SDLat.smulLat (1 : Matrix (Fin N) (Fin N) H.E) L = L := by
    intro L
    ext v
    simp [SDLat.smulLat]
  have hmul : ∀ (a b : Matrix (Fin N) (Fin N) H.E) (L : Submodule (𝓞 H.E) (Fin N → H.E)),
      SDLat.smulLat (a * b) L = SDLat.smulLat a (SDLat.smulLat b L) := by
    intro a b L
    unfold SDLat.smulLat
    rw [← Submodule.map_comp, Matrix.toLin'_mul]
    rfl
  refine exists_potential ((chi H).comp dt)
    (fun γ (L L' : SDLat H.E N) => L'.1 = SDLat.smulLat (γ : Matrix (Fin N) (Fin N) H.E) L.1)
    (fun L => (hone _).symm) (fun γ L L' h => ?_) (fun γ γ' L L' L'' h h' => ?_) (fun γ L h => ?_)
  · rw [h, ← hmul, ← Submonoid.coe_mul, inv_mul_cancel]
    exact (hone _).symm
  · rw [h', h, ← hmul]; rfl
  · refine chi_of_integral H _ (isIntegral_det L.1 L.2.1 L.2.2.1 _ fun v hv => ?_)
    rw [h]
    exact ⟨v, hv, rfl⟩

end Host

section Chain

open GlobalTheory.MemberTorsor

variable (B : Pre)

def uI : ℂˣ := Units.mk0 Complex.I Complex.I_ne_zero

theorem norm_uI_zpow (a b : ℤ) : ‖((uI ^ a * uI ^ b : ℂˣ) : ℂ)‖ = 1 := by
  simp [uI]

open Classical in

@[reducible] def ch (u : B.Word) : ColumnChain B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { chain B.R (Tau B.R) (B.hcW u) (B.T u) with
    rhoDet := fun i _ => ((uI⁻¹ * uI ^ (-(((B.R.N (i + 1)) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rhoDet' := fun i _ => ((uI * uI ^ ((((B.R.N i) / 2 : ℕ) : ℤ)) : ℂˣ) : ℂ)
    rho_norm := fun _ _ _ => by simp [uI]
    rho'_norm := fun _ _ _ => by simp [uI] }

open Classical in

@[reducible] def member (u : B.Word) : Member B.R (Tau B.R) (B.hcW u) :=
  haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
  { C := ch B u
    A := { atT B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) with
      duStar := B.duStar u, duStar_pos := B.duStar_pos u, Dstar := B.Dstar, Dstar_pos := B.Dstar_pos,
      GamP := B.GamP, one_lt_gammaP := B.one_lt_gammaP }
    P := { period B.R (Tau B.R) (B.hcW u) (B.T u) with } }

@[reducible] def cols0 : Cols0 B where
  mem := member B
  A_T _ := rfl
  A_duStar _ := rfl
  A_Dstar _ := rfl
  A_GamP _ := rfl
  clsLat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).L0
  clsLat_lat := letI := B.host.cmStar; fun _ i _ => (B.sp.X i).standardTuple_isLattice
  Tup := Fin 3
  mu0 := 0
  muStar := 1
  muStar' := 2
  chTw u _ := ch B u
  memberColumns_twistedChain_base _ := rfl
  e0Tw _ _ := LinearEquiv.refl ℂ _
  PTw u _ := (member B u).P
  Dt := ℂˣ
  detCls _ _ _ := uI
  muTil _ := MonoidHom.id _
  chiD := MonoidHom.id _
  UO := ⊥
  chiD_UO x hx := Subgroup.mem_bot.1 hx
  e1Dt := chi B.host
  rest_detCharacter_on_unitary_eq := chi_apply B.host
  relDet N L L' := QuotientGroup.mk (((exists_pot B.host N).choose L)⁻¹ * (exists_pot B.host N).choose L')
  relDet_self N L := by simp
  relDet_mul N L L' L'' := by
    rw [← QuotientGroup.mk_mul, mul_assoc, mul_inv_cancel_left]
  relDet_smul N L L' γ h := by rw [(exists_pot B.host N).choose_spec γ L L' h]
  rhoDet_eq_inv_muTilde_chiD_pow _ _ _ := rfl
  rhoDetPrime_eq_muTilde_mul_chi_pow _ _ _ := rfl

open Classical in

def cols (B : Base) : Cols B where
  toCols0 := cols0 B.toPre
  fm u :=
    haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    { forms B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) B.LL B.embLL B.places with }

theorem two_lt_alt (u : B.Word) : 2 < B.T u := by
  have h := B.level_mod_four _ (B.T_level u)
  have h2 := (B.T_prime u).two_le
  omega

open Classical in

theorem exists_cols (B : Base) : ∃ C : Cols B, (∀ u i, Nonempty ((C.mem u).C.cls i)) ∧
    (∀ u, (C.mem u).A.Mram ≠ ⊥) ∧ (∀ u i, (C.fm u).Fi i ≠ ⊥) ∧ C.mu0 ≠ C.muStar ∧ C.mu0 ≠ C.muStar' ∧
    C.muStar ≠ C.muStar' ∧ Function.Injective C.chiD ∧ ∀ u i c, C.chiD (C.detCls u i c) ≠ 1 := by
  refine ⟨cols B, fun u i => ⟨(1 : Tau B.R → (ZMod (B.T u))ˣ)⟩, fun u => ?_, fun u i => ?_,
    (by decide : (0 : Fin 3) ≠ 1), (by decide : (0 : Fin 3) ≠ 2), (by decide : (1 : Fin 3) ≠ 2),
    fun _ _ h => h, fun u i c h => ?_⟩
  · haveI : Fact (B.T u).Prime := ⟨B.T_prime u⟩
    exact mram_ne_bot B.R (Tau B.R) (B.hcW u) (B.T u) (card_Tau B.host) (two_lt_alt B.toPre u)
  · exact (top_ne_bot : (⊤ : Submodule ℂ ((Tau B.R → (ZMod (B.T u))ˣ) → Unit → ℂ)) ≠ ⊥)
  · have h' : uI = 1 := h
    have := congrArg (fun x : ℂˣ => (x : ℂ).re) h'
    simp [uI] at this

theorem nonempty_cols0 (B : Pre) : Nonempty (Cols0 B) := ⟨cols0 B⟩

theorem T_win (C : Cols0 B) (u : B.Word) : (C.mem u).A.Tstar ≤ ((C.mem u).A.T : ℝ) ∧
    ((C.mem u).A.T : ℝ) ≤ (1 + 1 / ((B.R.f : ℝ) * B.R.k)) * (C.mem u).A.Tstar := by
  unfold ColumnsAtT.Tstar ColumnsAtT.Xu
  rw [C.A_T, C.A_duStar, C.A_Dstar, C.A_GamP]
  exact B.T_win u

end Chain

end GlobalTheory.Mem.ColsModel

end
end

-- bundled from Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.InvariantDataMet
section
noncomputable section

open Matrix Formalism.DegreeFormula Formalism.MJ Formalism.UG Formalism.L2.Geo
open scoped ComplexOrder ContDiff

namespace GlobalTheory.HodgeDomain

variable {ι : Type} [Fintype ι] {p q : ℕ}

theorem smoothOn_det {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b) :
    SmoothOn fun z => (M z).det := by
  unfold SmoothOn at *
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

theorem smoothOn_inv {n : ℕ} {M : Pt ι p q → Matrix (Fin n) (Fin n) ℂ} (h : ∀ a b, SmoothOn fun z => M z a b)
    (hd : ∀ z ∈ DomI ι p q, (M z).det ≠ 0) (a b : Fin n) : SmoothOn fun z => (M z)⁻¹ a b := by
  have hadj : SmoothOn fun z => (M z).adjugate a b := by
    simp only [adjugate_apply]
    refine smoothOn_det fun i j => ?_
    by_cases e : i = b
    · simp only [e, updateRow_self]; exact contDiffOn_const
    · simp only [updateRow_ne e]; exact h i j
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul]
  exact ContDiffOn.mul (ContDiffOn.inv (smoothOn_det h) fun v hv => hd _ hv) hadj

theorem smoothOn_coord (τ : ι) (a : Fin p) (b : Fin q) : SmoothOn fun z : Pt ι p q => z τ a b :=
  (contDiff_apply ℝ ℂ (τ, a, b)).contDiffOn

theorem smoothOn_star {f : Pt ι p q → ℂ} (h : SmoothOn f) : SmoothOn fun z => star (f z) :=
  Complex.conjCLE.contDiff.comp_contDiffOn h

theorem smoothOn_hP (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => hP (z τ) a b := by
  simp only [hP, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_coord τ a k) (smoothOn_star (smoothOn_coord τ b k)))

theorem smoothOn_hQ (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => hQ (z τ) a b := by
  simp only [hQ, Matrix.sub_apply, Matrix.mul_apply, conjTranspose_apply]
  exact contDiffOn_const.sub (ContDiffOn.sum fun k _ =>
    ContDiffOn.mul (smoothOn_star (smoothOn_coord τ k a)) (smoothOn_coord τ k b))

theorem smoothOn_hP_inv (τ : ι) (a b : Fin p) : SmoothOn fun z : Pt ι p q => (hP (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hP τ) (fun _ hz => (hP_posDef (hz τ)).det_pos.ne') a b

theorem smoothOn_hQ_inv (τ : ι) (a b : Fin q) : SmoothOn fun z : Pt ι p q => (hQ (z τ))⁻¹ a b :=
  smoothOn_inv (smoothOn_hQ τ) (fun z hz => (show (hQ (z τ)).PosDef from hz τ).det_pos.ne') a b

def bergman (z : Pt ι p q) : Pt ι p q →ₗ[ℂ] Pt ι p q →ₗ⋆[ℂ] ℂ :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun ξ η => ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace)
    (fun _ _ _ => by simp [Matrix.mul_add, Matrix.add_mul, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])
    (fun _ _ _ => by simp [Matrix.mul_add, Finset.sum_add_distrib])
    (fun _ _ _ => by simp [Finset.mul_sum])

theorem bergman_apply (z ξ η : Pt ι p q) :
    bergman z ξ η = ∑ τ, ((hP (z τ))⁻¹ * ξ τ * (hQ (z τ))⁻¹ * (η τ)ᴴ).trace := rfl

theorem trace_pos {A : Matrix (Fin p) (Fin p) ℂ} {B : Matrix (Fin q) (Fin q) ℂ} (hA : A.PosDef) (hB : B.PosDef)
    (ξ : Matrix (Fin p) (Fin q) ℂ) : 0 ≤ (A * ξ * B * ξᴴ).trace ∧ (ξ ≠ 0 → 0 < (A * ξ * B * ξᴴ).trace) := by
  open MatrixOrder in
  obtain ⟨R, hR, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.1 hA.isStrictlyPositive
  open MatrixOrder in
  obtain ⟨S, hS, rfl⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_mul_star_self.1 hB.isStrictlyPositive
  have e : (star R * R * ξ * (S * star S) * ξᴴ).trace = ((R * ξ * S) * (R * ξ * S)ᴴ).trace := by
    simp only [star_eq_conjTranspose, conjTranspose_mul, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  rw [e]
  have h0 := (posSemidef_self_mul_conjTranspose (R * ξ * S)).trace_nonneg
  refine ⟨h0, fun hξ => lt_of_le_of_ne h0 fun h => hξ ?_⟩
  have h1 := trace_mul_conjTranspose_self_eq_zero_iff.1 h.symm
  have hR' := (isUnit_iff_isUnit_det _).1 hR
  have hS' := (isUnit_iff_isUnit_det _).1 hS
  have : R⁻¹ * (R * ξ * S) * S⁻¹ = ξ := by
    rw [Matrix.mul_assoc R, nonsing_inv_mul_cancel_left _ _ hR', mul_nonsing_inv_cancel_right _ _ hS']
  rw [← this, h1]; simp

theorem bergman_moeb {g : ι → GL (Fin p ⊕ Fin q) ℂ} (hg : g ∈ UpqI ι p q) {z : Pt ι p q} (hz : z ∈ DomI ι p q)
    (ξ η : Pt ι p q) :
    bergman (moebI g z) (fun τ => tanAct (g τ) (z τ) (ξ τ)) (fun τ => tanAct (g τ) (z τ) (η τ)) =
      bergman z ξ η := by
  rw [bergman_apply, bergman_apply]
  refine Finset.sum_congr rfl fun τ _ => ?_
  have hu : g τ ∈ Upq p q := hg τ (Set.mem_univ _)
  rw [← hP_inv_moeb hu (hz τ), ← hQ_moeb hu (hz τ), Matrix.mul_inv_rev, Matrix.mul_inv_rev]
  simp only [tanAct, conjTranspose_mul, Matrix.mul_assoc, conjTranspose_nonsing_inv, moebI]
  rw [trace_mul_comm (jW (g τ) (z τ))ᴴ]
  simp only [Matrix.mul_assoc]

def invariantData {Γ : Subgroup (ι → GL (Fin p ⊕ Fin q) ℂ)} (hΓ : Γ ≤ UpqI ι p q) (c : ι → ℝ) (hc : ∀ τ, 0 < c τ) :
    BdData ι p q Γ where
  m := 0
  nrm := fun i => i.elim0
  nrm_pos := fun i => i.elim0
  nrm_le := fun i => i.elim0
  nrm_smooth := fun i => i.elim0
  nrm_inv := fun i => i.elim0
  kae := bergman
  kae_herm := fun z hz ξ η => by
    rw [bergman_apply, bergman_apply, map_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    rw [starRingEnd_apply, ← trace_conjTranspose]
    simp only [conjTranspose_mul, conjTranspose_conjTranspose, (hP_inv_posDef (hz τ)).isHermitian.eq,
      (show (hQ (z τ)).PosDef from hz τ).inv.isHermitian.eq, Matrix.mul_assoc]
    rw [trace_mul_comm]
    simp only [Matrix.mul_assoc]
  kae_pos := fun z hz ξ hξ => by
    obtain ⟨τ, hτ⟩ := Function.ne_iff.1 hξ
    have H := fun σ => trace_pos (hP_inv_posDef (hz σ)) (show (hQ (z σ)).PosDef from hz σ).inv (ξ σ)
    rw [bergman_apply, Complex.re_sum]
    exact Finset.sum_pos' (fun σ _ => (Complex.nonneg_iff.1 (H σ).1).1)
      ⟨τ, Finset.mem_univ _, (Complex.pos_iff.1 ((H τ).2 hτ)).1⟩
  kae_smooth := fun ξ η => by
    simp only [bergman_apply, trace, diag_apply, Matrix.mul_apply]
    exact ContDiffOn.sum fun τ _ => ContDiffOn.sum fun a _ => ContDiffOn.sum fun b _ => ContDiffOn.mul
      (ContDiffOn.sum fun k _ => ContDiffOn.mul (ContDiffOn.sum fun l _ =>
        ContDiffOn.mul (smoothOn_hP_inv τ a l) contDiffOn_const) (smoothOn_hQ_inv τ k b)) contDiffOn_const
  kae_inv := fun γ hγ z hz ξ η => bergman_moeb (hΓ hγ) hz ξ η
  cst := 1
  cst_pos := one_pos
  cst_small := fun i => i.elim0
  metW := fun z τ => (c τ : ℂ) • (hP (z τ))⁻¹
  metOm := fun z τ => (c τ : ℂ) • hQ (z τ)
  metW_pos := fun z hz τ => (hP_inv_posDef (hz τ)).smul (by exact_mod_cast hc τ)
  metOm_pos := fun z hz τ => PosDef.smul (hz τ) (by exact_mod_cast hc τ)
  metW_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hP_inv τ a b)
  metOm_smooth := fun τ a b => ContDiffOn.mul contDiffOn_const (smoothOn_hQ τ a b)
  metW_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hP_inv_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]
  metOm_inv := fun γ hγ z hz τ => by
    rw [Matrix.mul_smul, Matrix.smul_mul, moebI, hQ_moeb (hΓ hγ τ (Set.mem_univ _)) (hz τ)]

example (ξ η : Pt ι p q) : bergman 0 ξ η = ∑ τ, (ξ τ * (η τ)ᴴ).trace := by
  simp [bergman_apply, hP, hQ]

end GlobalTheory.HodgeDomain
end
end

