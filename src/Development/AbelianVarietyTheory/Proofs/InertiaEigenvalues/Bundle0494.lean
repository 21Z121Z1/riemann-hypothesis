import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0472
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0017
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.Bundle0005
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0483
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0459
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0456
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0034
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdemNotMemFilVOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsCrystallineIffMemH1f
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BlockCharactersCrystallineOfRules
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0304
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0462
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineFrobeniusBijOnLettersDirectSum
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Module

namespace GlobalTheory.NL.PhiD

section General

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F)
    {LL : Type} [Field LL] [Algebra Qp LL]
    {V : Type} [AddCommGroup V] [Module LL V] [Module Qp V] [IsScalarTower Qp LL V]
    (ρ : Representation LL G V)

theorem mem_letter (τ : K₀ →ₐ[Qp] LL) (x : V ⊗[Qp] B) :
    x ∈ DcrisL PD ρ τ ↔ (∀ g, actVB PD ρ g x = x) ∧
      ∀ c : K₀, mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x = τ c • x := by
  simp [DcrisL, Dcris, Submodule.mem_iInf, sub_eq_zero]

theorem phi_injective : Function.Injective (φVB PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V) PD.φ.toLinearMap PD.φ_inj

theorem iota_injective : Function.Injective (ιV PD (LL := LL) (V := V)) :=
  Module.Flat.lTensor_preserves_injective_linearMap (M := V)
    (PD.ι.toLinearMap.restrictScalars Qp) PD.ι_inj

theorem phi_mem (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    ∀ x ∈ DcrisL PD ρ τ', φVB PD (LL := LL) x ∈ DcrisL PD ρ τ := by
  have h1 : ∀ g x, φVB PD (LL := LL) (actVB PD ρ g x) = actVB PD ρ g (φVB PD (LL := LL) x) := by
    intro g x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [actVB, φVB, PD.φ_comm]
    | add a b ha hb => simp only [map_add, ha, hb]
  have h2 : ∀ (c : K₀) (x : V ⊗[Qp] B),
      φVB PD (LL := LL) (mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) c x) =
      mulVB (K₀ := K₀) (B := B) (V := V) (LL := LL) (PD.σ c) (φVB PD (LL := LL) x) := by
    intro c x
    induction x using TensorProduct.induction_on with
    | zero => simp
    | tmul v b => simp [mulVB, φVB, PD.φ_K₀]
    | add a b ha hb => simp only [map_add, ha, hb]
  intro x hx
  rw [mem_letter] at hx ⊢
  refine ⟨fun g => by rw [← h1, hx.1], fun c => ?_⟩
  obtain ⟨c, rfl⟩ := PD.σ_bij.2 c
  rw [← h2, hx.2, map_smul, h]

theorem iSupIndep_letter : iSupIndep fun τ : K₀ →ₐ[Qp] LL => DcrisL PD ρ τ := by
  have h := iSupIndep.iInf
    (fun (c : K₀) (a : LL) => Module.End.eigenspace
      (mulVB (Qp := Qp) (K₀ := K₀) (B := B) (V := V) (LL := LL) c) a)
    (fun c => Module.End.eigenspaces_iSupIndep _)
  have h' := h.comp (f := fun τ : K₀ →ₐ[Qp] LL => (τ : K₀ → LL)) DFunLike.coe_injective
  refine h'.mono fun τ x hx => ?_
  simp only [Function.comp, Submodule.mem_iInf, Module.End.mem_eigenspace_iff]
  exact ((mem_letter PD ρ τ x).1 hx).2

variable [FiniteDimensional LL V] [IsDomain B]

theorem phi_bijOn (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ)
    (τ τ' : K₀ →ₐ[Qp] LL) (h : ∀ c, τ' c = τ (PD.σ c)) :
    Set.BijOn (φVB PD (LL := LL) (V := V)) (DcrisL PD ρ τ') (DcrisL PD ρ τ) := by
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine ⟨phi_mem PD ρ τ τ' h, (phi_injective PD).injOn, fun y hy => ?_⟩
  have hi : Function.Injective ((φVB PD (LL := LL) (V := V)).restrict (phi_mem PD ρ τ τ' h)) :=
    fun x y hxy => Subtype.ext (phi_injective PD (congrArg Subtype.val hxy))
  have hs := (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by
    rw [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV])).1 hi
  obtain ⟨x, hx⟩ := hs ⟨y, hy⟩
  exact ⟨x, x.2, congrArg Subtype.val hx⟩

theorem iSup_letter (hc : Nat.card (K₀ →ₐ[Qp] LL) = finrank Qp K₀) (hV : IsCrys PD ρ) :
    (⨆ τ : K₀ →ₐ[Qp] LL, DcrisL PD ρ τ) = Dcris PD ρ := by
  classical
  haveI := PD.finK₀
  haveI := GlobalTheory.Per.LetterDim.finite_Dcris PD ρ hV
  haveI : ∀ τ, FiniteDimensional LL ↥(DcrisL PD ρ τ) := fun τ =>
    Submodule.finiteDimensional_of_le (S₂ := Dcris PD ρ) inf_le_left
  refine Submodule.eq_of_le_of_finrank_eq (iSup_le fun τ => inf_le_left) ?_
  have hinj := (iSupIndep_letter PD ρ).dfinsupp_lsum_injective
  rw [Submodule.iSup_eq_range_dfinsupp_lsum, LinearMap.finrank_range_of_inj hinj]
  change finrank LL (DirectSum _ fun τ => ↥(DcrisL PD ρ τ)) = _
  rw [Module.finrank_directSum]
  simp only [GlobalTheory.Per.LetterDim.letter_eq PD ρ hc hV, Finset.sum_const, Finset.card_univ, smul_eq_mul]
  rw [← Nat.card_eq_fintype_card, hc]
  exact hV.symm

end General

theorem phi_letters : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (l : ℕ) [Fact l.Prime] (K : FinExt l) (s : ℕ) (LL : FinExt l) (h : Good K s LL), let W := (HW l).W K s LL h; ∀ T : Lt K LL, IsCrys ((D.loc l).PD K) T.ρ → (∀ i : Let K, Set.BijOn (φVB ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) (Di (HW l) h T (i - 1)) (Di (HW l) h T i)) ∧ (⨆ i : Let K, Di (HW l) h T i) = Dcris ((D.loc l).PD K) T.ρ ∧ iSupIndep (fun i : Let K => Di (HW l) h T i) ∧ Function.Injective (ιV ((D.loc l).PD K) (LL := ↥LL.1) (V := T.V)) := by
  intro D HW l _ K s LL h W T hV
  haveI := GlobalTheory.RegularRing.isDomain_of_tied (D.locT l) K
  have hc : Nat.card (↥(K0 K) →ₐ[ℚ_[l]] ↥LL.1) = finrank ℚ_[l] ↥(K0 K) := by
    rw [← Nat.card_eq_of_bijective _ W.emb_bij, Nat.card_zmod]
  refine ⟨fun i => phi_bijOn _ T.ρ hc hV _ _ fun c => ?_, ?_,
    (iSupIndep_letter ((D.loc l).PD K) T.ρ).comp W.emb_bij.1, iota_injective _⟩
  · have := AlgHom.congr_fun (W.emb_σ (i - 1)) c
    rw [sub_add_cancel] at this
    exact this.symm
  · rw [← iSup_letter _ T.ρ hc hV]
    exact W.emb_bij.2.iSup_comp (fun τ => DcrisL ((D.loc l).PD K) T.ρ τ)

end GlobalTheory.NL.PhiD
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePeriodsExtensionSpan
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per GlobalTheory.IndefiniteRowSideFullHecke.CrystallineSubrepresentation GlobalTheory.RegularRing

namespace GlobalTheory.Per.DcrisSpan

open GlobalTheory.Per.TiedRestrict

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}
variable {K K' LL : FinExt l} (h : K.1 ≤ K'.1) {V : Type} [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V]
  [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V)

theorem le_span_restrict (T : LocTied l P AI) (hc : IsCrys (P.PD K) ρ) :
    DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))) ≤
      Submodule.span ↥(K0 K') (↑(DcrisK₀ (P.PD K) ρ) : Set (P.R.B ⊗[ℚ_[l]] V)) := by
  have := LL.2
  have : IsDomain P.R.B := isDomain_of_tied T K
  have : FiniteDimensional ℚ_[l] V := Module.Finite.trans ↥LL.1 V
  have hc' := isCrys_restrict h ρ T hc
  obtain ⟨h1, -⟩ := finite_le₀ (P.PD K) (fracInv_of_tied T K) ρ
  obtain ⟨h2, -⟩ := finite_le₀ (P.PD K') (fracInv_of_tied T K') (ρ.comp (Subgroup.inclusion (GK_le h)))
  rw [isCrys_iff_finrank] at hc hc'
  let e := Module.finBasisOfFinrankEq ↥(K0 K) _ hc
  have hB := indepB (P.PD K) (fracInv_of_tied T K) ρ e e.linearIndependent
  let d : Fin (Module.finrank ℚ_[l] V) → ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))) :=
    fun i => ⟨e i, dcris_le h ρ (e i).2⟩
  have hd : LinearIndependent ↥(K0 K') d :=
    LinearIndependent.of_comp (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype
      (hB.restrict_scalars' ↥(K0 K'))
  have htop : Submodule.span ↥(K0 K') (Set.range d) = ⊤ :=
    Submodule.eq_top_of_finrank_eq (by rw [finrank_span_eq_card hd]; simpa using hc'.symm)
  intro x hx
  have hx' : (⟨x, hx⟩ : ↥(DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h))))) ∈
      Submodule.span ↥(K0 K') (Set.range d) := by
    rw [htop]; trivial
  have hm := Submodule.apply_mem_span_image_of_mem_span
    (DcrisK₀ (P.PD K') (ρ.comp (Subgroup.inclusion (GK_le h)))).subtype hx'
  refine Submodule.span_mono ?_ hm
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  exact (e i).2

theorem dcris_span : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), IsStd P AI →
    ∀ (LL : FinExt l) (T : QLat LL) (K K'' : FinExt l), K.1 ≤ K''.1 → IsCrys (P.PD K) (T.ρ.comp (inclG K)) →
      DcrisK₀ (P.PD K'') (T.ρ.comp (inclG K'')) ≤
        Submodule.span ↥(K0 K'') (↑(DcrisK₀ (P.PD K) (T.ρ.comp (inclG K))) : Set (P.R.B ⊗[ℚ_[l]] T.V)) := by
  intro l _ P AI hS LL T K K'' h hc
  have eρ : T.ρ.comp (inclG K'') = (T.ρ.comp (inclG K)).comp (Subgroup.inclusion (GK_le h)) :=
    MonoidHom.ext fun _ => rfl
  rw [eρ]
  exact le_span_restrict h _ hS.some hc

end GlobalTheory.Per.DcrisSpan
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallinePhiModuleMapExists
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.BKGal.CrysEps

theorem shift_C {K : Type} [Field K] [CharZero K] (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (h : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (k : K) : sh (PowerSeries.C k) = PowerSeries.C (PowerSeries.C k) := by
  refine PowerSeries.ext fun i => ?_
  cases i with
  | zero => simpa using h (PowerSeries.C k) 0
  | succ n =>
    have h1 := h (PowerSeries.C k) (n + 1)
    rw [Function.iterate_succ_apply, PowerSeries.derivative_C,
      Function.iterate_fixed (map_zero _)] at h1
    have h2 : ((n + 1).factorial : K⟦X⟧) ≠ 0 := by
      rw [← map_natCast (PowerSeries.C : K →+* K⟦X⟧), Ne,
        map_eq_zero_iff _ PowerSeries.C_injective]
      exact Nat.cast_ne_zero.2 (Nat.factorial_ne_zero _)
    rw [(mul_eq_zero.1 h1).resolve_left h2, PowerSeries.coeff_C, if_neg (Nat.succ_ne_zero n)]

theorem bc_induction {A B M N : Type} [CommRing A] [CommRing B] [AddCommGroup M] [Module A M]
    [AddCommGroup N] [Module B N] {f : A →+* B} {u : M →ₛₗ[f] N} (h : SemiBC u) (p : N → Prop)
    (h0 : p 0) (hadd : ∀ y z, p y → p z → p (y + z)) (hs : ∀ (r : B) y, p y → p (r • y))
    (hu : ∀ x, p (u x)) (y : N) : p y := by
  first
  | (rename_i h_4 h_5 h_6 h_7 h_8 h_9; revert A B M N h_4 h_5 h_6 h_7 h_8 h_9 f u h p h0 hadd hs hu y; exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction)
  | exact @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction
  | (apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply _root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> assumption)
  | (intros; apply @_root_.GlobalTheory.BaseChangeInduction.baseChange_induction <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.BaseChangeInduction.baseChange_induction ..)

theorem exists_crystalline_epsilon_combination {l : ℕ} [Fact l.Prime] {a e : ℕ} {O K : Type} [CommRing O] [NormedField K]
    [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [CharZero K] {ι : Type} [Fintype ι] [DecidableEq ι]
    {R : Type} [CommRing R] (Q : Obj l R) (toA : Q.A → ZMod a → K⟦X⟧) {J : Type} [Fintype J] (o : J → O)
    (hspan : ∀ f : ZMod a → K⟦X⟧, (∀ τ, f τ ∈ A O K) → ∃ w : J → Q.A, ∀ τ,
      f τ = ∑ k, PowerSeries.C (algebraMap O K (o k)) * toA (w k) τ)
    (P : PhiMod O K l e a ι) (EE : FCrys l R) (c : EE.M Q →+ Vec K a ι) (hinj : Function.Injective c)
    (hmem : ∀ x, c x ∈ P.M) (hsurj : ∀ m ∈ P.M, ∃ x, c x = m)
    (hw : ∀ (w : Q.A) (x : EE.M Q), c (w • x) = fun τ i => toA w τ * c x τ i)
    (hU : ∀ o : O, ∃ U : FHom EE EE, ∀ x,
      c (U.u Q x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i)
    (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧)
    (hsh : ∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f)
    (PP : Obj l R) (p₀ p₁ : GlobalTheory.Prism.Hom Q PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧)
    (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧))
    (hl₀ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i)
    (hl₁ : ∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i)
    (ht₀ : ∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i)))
    (ht₁ : ∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) :
    ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  have hb : ∀ k : ι, (fun _ => Pi.single k 1 : Vec K a ι) ∈ P.M := fun k => mem_tot.2 fun τ i => by
    rcases eq_or_ne i k with rfl | h
    · simp only [Pi.single_eq_same]; exact one_mem _
    · simp only [Pi.single_eq_of_ne h]; exact zero_mem _
  choose b hb using fun k => hsurj _ (hb k)
  choose U hU using hU
  refine ⟨fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i, ?_⟩
  set ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧ := fun τ => Matrix.of fun i k => lam₀ (EE.tr p₁ (b k)) τ i with hε

  have hU₀ : ∀ o y τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i := by
    intro o y
    refine bc_induction (EE.tr_bc p₀) (fun y => ∀ τ i, lam₀ ((U o).u PP y) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₀ y τ i) ?_ ?_ ?_ ?_ y
    · intro τ i; simp
    · intro y z hy hz τ i
      simp only [map_add, Pi.add_apply, hy, hz, mul_add]
    · intro r y hy τ i
      rw [map_smul, hl₀, hl₀, hy]; ring
    · intro x τ i
      rw [(U o).u_tr, ht₀, ht₀, hU]
      simp only [map_mul, frob_C]
  have hU₁ : ∀ o x τ i, lam₁ ((U o).u PP (EE.tr p₁ x)) τ i =
      PowerSeries.C (PowerSeries.C (algebraMap O K o)) * lam₁ (EE.tr p₁ x) τ i := by
    intro o x τ i
    rw [(U o).u_tr, ht₁, ht₁, hU]
    simp only [map_mul, frob_C, shift_C sh hsh]
  have hS0 : ∀ τ, lam₀ 0 τ = ε τ *ᵥ lam₁ 0 τ := by intro τ; simp
  have hSadd : ∀ y z, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) → (∀ τ, lam₀ z τ = ε τ *ᵥ lam₁ z τ) →
      ∀ τ, lam₀ (y + z) τ = ε τ *ᵥ lam₁ (y + z) τ := by
    intro y z hy hz τ
    simp only [map_add, Pi.add_apply, hy, hz, Matrix.mulVec_add]
  have hSs : ∀ (r : PP.A) y, (∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) →
      ∀ τ, lam₀ (r • y) τ = ε τ *ᵥ lam₁ (r • y) τ := by
    intro r y hy τ
    have e0 : lam₀ (r • y) τ = j τ r • lam₀ y τ := funext fun i => hl₀ r y τ i
    have e1 : lam₁ (r • y) τ = j τ r • lam₁ y τ := funext fun i => hl₁ r y τ i
    rw [e0, e1, hy, Matrix.mulVec_smul]
  have hSU : ∀ o x, (∀ τ, lam₀ (EE.tr p₁ x) τ = ε τ *ᵥ lam₁ (EE.tr p₁ x) τ) →
      ∀ τ, lam₀ (EE.tr p₁ ((U o).u _ x)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ ((U o).u _ x)) τ := by
    intro o x hx τ
    rw [← (U o).u_tr]
    have e0 : lam₀ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₀ (EE.tr p₁ x) τ :=
      funext fun i => hU₀ o _ τ i
    have e1 : lam₁ ((U o).u PP (EE.tr p₁ x)) τ =
        (PowerSeries.C (PowerSeries.C (algebraMap O K o)) : K⟦X⟧⟦X⟧) • lam₁ (EE.tr p₁ x) τ :=
      funext fun i => hU₁ o _ τ i
    rw [e0, e1, hx, Matrix.mulVec_smul]
  have hSb : ∀ k τ, lam₀ (EE.tr p₁ (b k)) τ = ε τ *ᵥ lam₁ (EE.tr p₁ (b k)) τ := by
    intro k τ
    have e1 : lam₁ (EE.tr p₁ (b k)) τ = Pi.single k 1 := funext fun i => by
      rw [ht₁, hb]
      rcases eq_or_ne i k with rfl | h
      · simp only [Pi.single_eq_same, map_one]
      · simp only [Pi.single_eq_of_ne h, map_zero]
    rw [e1, Matrix.mulVec_single_one]
    rfl
  refine bc_induction (EE.tr_bc p₁) (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hS0 hSadd hSs fun x => ?_
  choose w hwx using fun i => hspan (fun τ => c x τ i) fun τ => mem_tot.1 (hmem x) τ i
  have hx : x = ∑ i, ∑ k, (U (o k)).u _ (w i k • b i) := by
    apply hinj
    funext τ i
    simp only [map_sum, Finset.sum_apply, hU, hw, hb]
    rw [Finset.sum_eq_single i]
    · simp only [Pi.single_eq_same, mul_one]
      exact hwx i τ
    · intro i' _ h
      simp only [Pi.single_eq_of_ne h.symm, mul_zero, Finset.sum_const_zero]
    · simp
  rw [hx, map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun i _ => ?_
  rw [map_sum]
  refine Finset.sum_induction _ (fun y => ∀ τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ) hSadd hS0 fun k _ => ?_
  refine hSU _ _ ?_
  rw [LinearMap.map_smulₛₗ]
  exact hSs _ _ (hSb i)

theorem exists_eps : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (EE : FCrys l ↥(OL (ϖ.field a))) (c : EE.M (ϖ.prism a) →+ Vec K a ι), Function.Injective c → (∀ x, c x ∈ P.M) → (∀ m ∈ P.M, ∃ x, c x = m) → (∀ (w : (ϖ.prism a).A) (x : EE.M (ϖ.prism a)), c (w • x) = fun τ i => (toAc t K w τ : K⟦X⟧) * c x τ i) → (∀ o : O, ∃ U : FHom EE EE, ∀ x, c (U.u (ϖ.prism a) x) = fun τ i => PowerSeries.C (algebraMap O K o) * c x τ i) → ∀ (sh : K⟦X⟧ →+* K⟦X⟧⟦X⟧), (∀ (f : K⟦X⟧) (i : ℕ), (i.factorial : K⟦X⟧) * coeff i (sh f) = (PowerSeries.derivative K)^[i] f) → ∀ (PP : Obj l ↥(OL (ϖ.field a))) (p₀ p₁ : GlobalTheory.Prism.Hom (ϖ.prism a) PP) (j : ZMod a → PP.A →+* K⟦X⟧⟦X⟧), (∀ τ (x : (Wq l a)⟦X⟧), j τ (p₀.f x) = PowerSeries.C (toAc t K (frobS l a x) τ : K⟦X⟧) ∧ j τ (p₁.f x) = sh (toAc t K (frobS l a x) τ : K⟦X⟧)) → ∀ (lam₀ lam₁ : EE.M PP →+ (ZMod a → ι → K⟦X⟧⟦X⟧)), (∀ (r : PP.A) (y : EE.M PP) τ i, lam₀ (r • y) τ i = j τ r * lam₀ y τ i) → (∀ (r : PP.A) (y : EE.M PP) τ i, lam₁ (r • y) τ i = j τ r * lam₁ y τ i) → (∀ x τ i, lam₀ (EE.tr p₀ x) τ i = PowerSeries.C (frob K l (c x (τ - 1) i))) → (∀ x τ i, lam₁ (EE.tr p₁ x) τ i = sh (frob K l (c x (τ - 1) i))) → ∃ ε : ZMod a → Matrix ι ι K⟦X⟧⟦X⟧, ∀ y τ, lam₀ y τ = ε τ *ᵥ lam₁ y τ := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j _
    lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  haveI : CharZero K := charZero_of_injective_algebraMap (algebraMap ℚ_[l] K).injective
  refine exists_crystalline_epsilon_combination (ϖ.prism a) (fun w τ => (toAc t K w τ : K⟦X⟧)) (Module.Free.chooseBasis ℤ_[l] O) ?_
    P EE c hinj hmem hsurj hw hU sh hsh PP p₀ p₁ j lam₀ lam₁ hl₀ hl₁ ht₀ ht₁
  intro f hf
  obtain ⟨w, hw⟩ := exists_eq_sum_toAc t K (Module.Free.chooseBasis ℤ_[l] O) fun τ => ⟨f τ, hf τ⟩
  refine ⟨w, fun τ => ?_⟩
  refine (congrArg Subtype.val (congrFun hw τ)).trans ?_
  rw [Finset.sum_apply, AddSubmonoidClass.coe_finset_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Pi.smul_apply, Subalgebra.coe_smul, Algebra.smul_def, algebraMap_eq_C]

end GlobalTheory.BKGal.CrysEps
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CuspOfGoodRow
section
open Formalism.BasicNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain GlobalTheory.IndefiniteRowSideFullHecke.CMTypeEmbeddings GlobalTheory.RowCuspPar Polynomial

noncomputable section

namespace GlobalTheory.RowCuspLabels

theorem cusp_of_goodRow : ∀ (D : D7) (S : GlobalTheory.HeightCounting.RowSide D), Formalism.MainNotions.SumRepresentations.At.TieLab D.nd D.naut → ∀ (σ : D.what₂.FT),
  D.nd.goodRow σ → ∀ (Sig : List (Part D.naut.CG)), (∀ p ∈ Sig, 1 ≤ p.a ∧ 1 ≤ p.d) →
  rankIso D.nd D.naut Sig = D.R.r →
  (∀ w, IsSplitPl D.host w → isoLoc D.nd D.naut Sig w = S.locR σ w) →
  IsCuspIso D.nd D.naut Sig := by
  intro D S hT σ hg Sig hpos hrank hloc
  let k : Fin 2 := 0
  have : Fact (D.host.g k).Prime := ⟨D.host.g_prime k⟩
  obtain ⟨h1, h2, -, -, h5, -⟩ := (hg k).1
  have : Nonempty (D.nd.PlG k) := by
    rw [← Fintype.card_pos_iff, D.nd.card_PlG k]
    show 0 < 2 * D.R.ord
    have := D.R.toFrame.ord_pos
    omega
  have hr : 1 ≤ D.R.r := by
    have := D.R.two_le_m
    show 1 ≤ D.R.k + D.R.m - 1
    omega
  have hf : ∀ v, D.nd.lab k σ v = ∏ j : Fin Sig.length,
      D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d := by
    intro v
    rw [S.lab_eq k σ v, ← hloc _ (GlobalTheory.Proof.SplitPlaceGoodSignature.typePlSplit D.nd D.naut k v),
      Formalism.MainNotions.SumRepresentations.inertiaCharpoly_eq_of_iso D.nd D.naut hT,
      Formalism.MainNotions.SumRepresentations.list_prod_fin Sig (fun p => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG p.π (D.naut.plGw k v)) ^ p.d)]
  have hrk : ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d = D.R.r := by
    rw [← hrank, rankIso, Formalism.MainNotions.SumRepresentations.list_sum_fin Sig (fun p => p.a * p.d)]
  have hd : ∀ j : Fin Sig.length, 1 ≤ (Sig.get j).a ∧ 1 ≤ (Sig.get j).d :=
    fun j => hpos _ (List.get_mem Sig j)
  have hdeg : ∀ v (j : Fin Sig.length),
      (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree =
        (Sig.get j).a := by
    intro v
    have hne : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v)) ^ (Sig.get j).d ≠ 0 := by
      rw [← Finset.prod_ne_zero_iff, ← hf v]
      exact (h1 v).1.ne_zero
    have hsum : ∑ j : Fin Sig.length,
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d =
        ∑ j : Fin Sig.length, (Sig.get j).a * (Sig.get j).d := by
      rw [hrk, ← (h1 v).2.1, hf v, natDegree_prod _ _ hne]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [natDegree_pow, mul_comm]
    have hle : ∀ j ∈ (Finset.univ : Finset (Fin Sig.length)),
        (D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))).natDegree *
          (Sig.get j).d ≤ (Sig.get j).a * (Sig.get j).d := by
      intro j _
      refine Nat.mul_le_mul_right _ ?_
      have := hT.2 k v (D.naut.locG (Sig.get j).π (D.naut.plGw k v))
      rwa [D.naut.locG_dim] at this
    intro j
    have := (Finset.sum_eq_sum_iff_of_le hle).1 hsum j (Finset.mem_univ j)
    exact Nat.eq_of_mul_eq_mul_right (hd j).2 this
  obtain ⟨hc, hall⟩ := Formalism.IrreducibleCountingLemmas.Z.good_cuspidal_multiplicity_one (ZMod (D.host.g k)) (D.nd.PlG k) D.R.r (D.nd.lab k σ)
    (Fin Sig.length) (fun j => (Sig.get j).a) (fun j => (Sig.get j).d)
    (fun v j => D.naut.items₂ k (D.naut.plGw k v) (D.naut.locG (Sig.get j).π (D.naut.plGw k v))) hr
    (fun v => (h1 v).2.1) h2 hf hdeg (fun j => (hd j).1) (fun j => (hd j).2)
    (by
      rintro ⟨a, ha1, ha2, ha⟩
      obtain ⟨v, hv⟩ := h5 a ha1 ha2
      exact hv (ha v))
  rw [Fintype.card_fin] at hc
  obtain ⟨p, rfl⟩ := List.length_eq_one_iff.1 hc
  obtain ⟨hd1, ha1⟩ := hall ⟨0, by simp⟩
  obtain ⟨a, π, d⟩ := p
  simp only [List.get_eq_getElem, List.getElem_cons_zero] at hd1 ha1
  subst hd1 ha1
  exact ⟨π, rfl⟩

end GlobalTheory.RowCuspLabels

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CycZpowCrysDRJump
section
noncomputable section

namespace GlobalTheory.CycPow

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct Module

section Generic

variable {G : Type} [Group G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B F : Type} [CommRing B] [CommRing F] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp F] [Algebra K₀ F] [Algebra K F] [IsScalarTower Qp K F]
    [IsScalarTower K₀ K F] [IsScalarTower Qp K₀ F]
    (PD : PeriodData G Qp K₀ K B F) {LL : Type} [Field LL] [Algebra Qp LL]

theorem step (u : F) (hu : PD.ι PD.t * u = 1) (hu' : u ∈ PD.Fil (-1)) (n : ℤ) :
    finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ (n + 1)))) =
        finrank LL ↥(DdR PD (charRep (cycLL PD LL ^ n))) ∧
      ∀ (τ : K →ₐ[Qp] LL) (a : ℤ), finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ (n + 1))) τ (a - 1)) =
        finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ n)) τ a) := by
  have htw : IsTwistRep (cycLL PD LL) (charRep (cycLL PD LL ^ n)) (charRep (cycLL PD LL ^ (n + 1))) := by
    refine ⟨LinearEquiv.refl LL LL, fun g x => ?_⟩
    rw [zpow_add_one]
    change (((cycLL PD LL ^ n) g * cycLL PD LL g : LLˣ) : LL) * x =
      ((cycLL PD LL g : LLˣ) : LL) * ((((cycLL PD LL ^ n) g : LLˣ) : LL) * x)
    rw [Units.val_mul]
    ring
  obtain ⟨Φ, hD, hF⟩ := GlobalTheory.DRFil.exists_twist_equiv PD _ _ htw u hu hu'
  exact ⟨by rw [← hD, LinearEquiv.finrank_map_eq], fun τ a => by rw [← hF, LinearEquiv.finrank_map_eq]⟩

theorem isDR_and_finrank [CharZero Qp] [FiniteDimensional Qp LL] (u : F) (hu : PD.ι PD.t * u = 1)
    (hu' : u ∈ PD.Fil (-1)) (k : ℤ) :
    IsDR PD (charRep (cycLL PD LL ^ k)) ∧ ∀ (τ : K →ₐ[Qp] LL) (a : ℤ),
      finrank LL ↥(FildR PD (charRep (cycLL PD LL ^ k)) τ a) = if a ≤ -k then 1 else 0 := by
  induction k using Int.induction_on with
  | zero =>
    have h1 : charRep (1 : G →* LLˣ) = Representation.trivial LL G LL := by
      ext g
      simp [charRep]
    rw [zpow_zero, h1, neg_zero]
    exact ⟨GlobalTheory.CrysExt.isDR_trivial PD, GlobalTheory.CrysExt.finrank_fildR_trivial PD⟩
  | succ n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' n
    refine ⟨h1.trans ih.1, fun τ a => ?_⟩
    have h3 := h2 τ (a + 1)
    rw [add_sub_cancel_right] at h3
    rw [h3, ih.2]
    exact if_congr (by omega) rfl rfl
  | pred n ih =>
    obtain ⟨h1, h2⟩ := step PD (LL := LL) u hu hu' (-(n : ℤ) - 1)
    rw [sub_add_cancel] at h1 h2
    refine ⟨h1.symm.trans ih.1, fun τ a => ?_⟩
    rw [← h2, ih.2]
    exact if_congr (by omega) rfl rfl

end Generic

theorem cyc_zpow_crys_dR_jump : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (k : ℤ), IsCrys (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ IsDR (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) ∧ ∀ (τ : ↥K.1 →ₐ[ℚ_[l]] ↥LL.1) (a : ℤ), multV (P.PD K) (charRep (cycLL (P.PD K) ↥LL.1 ^ k)) τ a = if a = -k then 1 else 0 := by
  intro l _ P AI T K LL k
  have := LL.2
  obtain ⟨u, hu', hu⟩ := ((GlobalTheory.MemLoc.TiedUnif.tied_uniformiser l P AI T).2.2 K (-1) 1).1
    (by rw [neg_add_cancel]; exact (P.PD K).one_mem)
  have ht : (P.PD K).ι (P.PD K).t * u = 1 := by
    rw [P.PD_ι, P.period_datum_t_eq]
    exact hu.symm
  obtain ⟨h1, h2⟩ := isDR_and_finrank (P.PD K) (LL := ↥LL.1) u ht hu' k
  refine ⟨GlobalTheory.BlockCrys.isCrys_cyc_zpow _ k, h1, fun τ a => ?_⟩
  rw [multV, h2, h2]
  split_ifs <;> first | rfl | omega

end GlobalTheory.CycPow
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DiscBoundedFunctionIsPowerSeriesStatement
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.disc_bounded_function_isPowerSeries : ∀ (l : ℕ) [Fact l.Prime] (K : FinExt l) (bk : BK K) (ρ : ℝ≥0), 0 < ρ → ρ < 1 → ∀ y : bk.DS ρ, (∀ ρ₁ : ℝ≥0, ρ₁ < 1 → ∃ (ρ' : ℝ≥0) (R : bk.DS ρ' →+* bk.DS ρ) (y' : bk.DS ρ'), ρ₁ ≤ ρ' ∧ ρ ≤ ρ' ∧ ρ' < 1 ∧ IsDiscMap (RingHom.id bk.S) R ∧ R y' = y ∧ ‖y'‖ ≤ 1) → ∃ a, toDisc l (X : bk.S) ρ a = y := by
  first | exact @GlobalTheory.BSP.disc_bdd_isSeries | exact GlobalTheory.BSP.disc_bdd_isSeries | (intros; apply GlobalTheory.BSP.disc_bdd_isSeries <;> assumption)
end

