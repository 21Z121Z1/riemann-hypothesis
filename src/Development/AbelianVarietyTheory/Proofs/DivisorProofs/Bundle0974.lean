import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.FWExist
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0035
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0947
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0724
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CuspidalCharacterFormula
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HarishChandraSeriesLabelExistsUniqueGLn
import Development.AbelianVarietyTheory.Definitions.ExistenceOfLattices.Bundle0001
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0078
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.Bundle0082
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0034
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0026
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MvIsIntMapMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0948
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0607
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0636
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0642
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0637
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0937
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0949
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0901
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import GroundTheory.AutomorphicForms.MultiplicityOne.Bundle0001
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0928
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0863

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LMLatOfLIntegral
section
noncomputable section

open NumberField IsDedekindDomain Module

namespace GlobalTheory.GoodLat

section General

variable {R K V : Type} [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K]
  [AddCommGroup V] [Module K V] [Module R V] [IsScalarTower R K V]

theorem exists_smul_mem (N : Submodule R V) {x : V} (hx : x ∈ Submodule.span K (N : Set V)) :
    ∃ a : R, a ≠ 0 ∧ a • x ∈ N := by
  first
  | (rename_i h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11; revert R K V h_3 h_4 h_5 h_6 h_7 h_8 h_9 h_10 h_11 N x hx; exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span)
  | exact @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span
  | (apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> assumption)
  | (intros; apply @_root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.NonzeroScalarInSpan.exists_ne_zero_smul_mem_of_mem_span ..)

theorem isLattice_comap [IsNoetherianRing R] {U : Type} [AddCommGroup U] [Module K U] [Module R U] [IsScalarTower R K U]
    (N : Submodule R V) (hN : Submodule.IsLattice K N) (f : U →ₗ[K] V) (hf : Function.Injective f) :
    Submodule.IsLattice K (N.comap (f.restrictScalars R)) := by
  refine ⟨?_, ?_⟩
  · refine Submodule.fg_of_fg_map_injective (f.restrictScalars R) hf ?_
    exact hN.fg.of_le (Submodule.map_comap_le _ _)
  · rw [eq_top_iff]
    intro x _
    obtain ⟨a, ha, hax⟩ := exists_smul_mem (K := K) N (x := f x) (hN.span_eq_top ▸ Submodule.mem_top)
    have ha1 : algebraMap R K a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective R K)).2 ha
    have e : x = (algebraMap R K a)⁻¹ • (a • x) := by
      rw [← algebraMap_smul K a x, smul_smul, inv_mul_cancel₀ ha1, one_smul]
    rw [e]
    refine Submodule.smul_mem _ _ (Submodule.subset_span ?_)
    show (f.restrictScalars R) (a • x) ∈ N
    rw [map_smul]
    exact hax

end General

section Forms

open Formalism.IndefR.Arith

variable {LL Ks : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks] [Algebra Ks LL]
variable {WL : Type} [AddCommGroup WL] [Module LL WL] [Module Ks WL] [IsScalarTower Ks LL WL]
  [Module (𝓞 LL) WL] [IsScalarTower (𝓞 LL) LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL]
variable {W : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
variable {G0 : Type} [Group G0] [Fintype G0]
variable (A : FormsL LL Ks WL W G0)

omit [Fintype G0] in

theorem isLattice_span_MK (hK : A.IsKsForm) (hM : A.MKFull) :
    Submodule.IsLattice LL (Submodule.span (𝓞 LL) (A.MK : Set WL)) := by
  obtain ⟨⟨s, hs⟩, hsp⟩ := hM
  refine ⟨⟨s, le_antisymm (Submodule.span_mono (hs ▸ Submodule.subset_span)) (Submodule.span_le.2 ?_)⟩, ?_⟩
  · intro x hx
    rw [← hs] at hx
    induction hx using Submodule.span_induction with
    | mem x hx => exact Submodule.subset_span hx
    | zero => exact Submodule.zero_mem _
    | add x y _ _ ihx ihy => exact Submodule.add_mem _ ihx ihy
    | smul a x _ ih =>
      have e : a • x = (algebraMap (𝓞 Ks) (𝓞 LL) a) • x := by
        rw [← algebraMap_smul Ks a x, ← algebraMap_smul LL (algebraMap (𝓞 Ks) Ks a) x,
          ← algebraMap_smul LL (algebraMap (𝓞 Ks) (𝓞 LL) a) x]
        rfl
      rw [SetLike.mem_coe, e]
      exact Submodule.smul_mem _ _ ih
  · obtain ⟨n, b, hb, -, -, -, h4⟩ := hK
    rw [eq_top_iff, ← h4, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    have h1 : b i ∈ Submodule.span Ks (A.MK : Set WL) := hsp ▸ hb i
    exact Submodule.span_mono Submodule.subset_span (Submodule.span_le_restrictScalars Ks LL _ h1)

theorem isLattice_Mcoord (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL)
    {d : ℕ} (b : Fin d → WL) (hb : LinearIndependent LL b) (hW : ∀ i, b i ∈ A.Wgood J0 lam0 eC) :
    Submodule.IsLattice LL (A.Mcoord J0 lam0 eC b) := by
  have e : A.Mcoord J0 lam0 eC b = (Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((Fintype.linearCombination LL b).restrictScalars (𝓞 LL)) := by
    ext c
    have hc : Fintype.linearCombination LL b c ∈ A.Wgood J0 lam0 eC := by
      rw [Fintype.linearCombination_apply]
      exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hW i)
    exact ⟨fun h => h.1.1, fun h => ⟨⟨h, hc.1⟩, hc.2⟩⟩
  rw [e]
  refine isLattice_comap _ (isLattice_span_MK A hK hM) _ ?_
  refine LinearMap.ker_eq_bot.1 (LinearMap.ker_eq_bot'.2 fun c hc => funext ?_)
  exact Fintype.linearIndependent_iff.1 hb c hc

theorem mj_full (hK : A.IsKsForm) (hM : A.MKFull) (J0 : Subgroup G0) (lam0 : J0 →* LLˣ) (eC : G0 → LL) :
    (A.Mj J0 lam0 eC).FG ∧ Submodule.span LL (A.Mj J0 lam0 eC : Set WL) = A.Wgood J0 lam0 eC := by
  have h := isLattice_comap _ (isLattice_span_MK A hK hM) (A.Wgood J0 lam0 eC).subtype Subtype.val_injective
  have e : A.Mj J0 lam0 eC = ((Submodule.span (𝓞 LL) (A.MK : Set WL)).comap
      ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL))).map
        ((A.Wgood J0 lam0 eC).subtype.restrictScalars (𝓞 LL)) := by
    ext x
    exact ⟨fun hx => ⟨⟨x, hx.1.2, hx.2⟩, hx.1.1, rfl⟩, by rintro ⟨y, hy, rfl⟩; exact ⟨⟨hy, y.2.1⟩, y.2.2⟩⟩
  refine ⟨e ▸ h.fg.map _, ?_⟩
  rw [e]
  show Submodule.span LL ((A.Wgood J0 lam0 eC).subtype '' _) = _
  rw [Submodule.span_image, h.span_eq_top, Submodule.map_subtype_top]

end Forms

section Record

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.Arith Formalism.IndefR.FWT Formalism.L2.Pj

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}

theorem mLat_of_full {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (F : Face D A)
    (hK : ∀ i, (R.FW i).IsKsForm) (hM : ∀ i, (R.FW i).MKFull) (b : Bool) : (R.toCx F).MLat b := fun i =>
  isLattice_Mcoord (R.FW i) (hK i) (hM i) _ _ _ (R.bL F b i)
    ((Module.finBasis D.what₂.LL (R.WL F b i)).linearIndependent.map' (R.WL F b i).subtype (Submodule.ker_subtype _))
    fun k => (Module.finBasis D.what₂.LL (R.WL F b i) k).2

variable {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)}
  {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

theorem mkFull_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (i : Fin D.R.m) : (R.FW i).MKFull := by
  refine mkFull_of _ ((R.FW i).WK.subtype ∘ₗ (t.e i).toLinearMap) ?_ (fun x => ?_) (hl i)
  · rw [LinearMap.range_comp, LinearEquiv.range, Submodule.map_subtype_top]
  · constructor
    · intro hx
      obtain ⟨f, hf⟩ := (t.e i).surjective ⟨x, hx.1⟩
      have hfx : ((t.e i f : (R.FW i).WK) : Fin (R.nW i) → D.what₂.LL) = x := congrArg Subtype.val hf
      have h1 := (t.mem_MK i f).1 (hfx ▸ hx)
      exact ⟨f, fun la v hv => h1 la ⟨v, hv⟩, hfx⟩
    · rintro ⟨f, hf, rfl⟩
      exact (t.mem_MK i f).2 fun la y => hf la y.1 y.2

theorem mLat_of_tie (t : FWTie T R κ v₀) (hl : LatFull T κ) (F : Face D A) (b : Bool) : (R.toCx F).MLat b :=
  mLat_of_full R F t.ks (mkFull_of_tie t hl) b

end Record

end GlobalTheory.GoodLat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LabelledCharactersEqAndCongrPrimeToPartStatement
section
open Polynomial GlobalTheory.IndefiniteRowSideFullHecke.LevelCuspCharacters GlobalTheory.ParamLabel
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.labelled_characters_eq_and_congr_primeToPart : ∀ (p : ℕ) [Fact p.Prime] (L : GlobalTheory.GLq.LabelDatum p) (d : ℕ), 0 < d → ∀ (θ θ' : Tor p d →* ℂˣ) (x x' : Fbar p), LabelsChar L θ x → LabelsChar L θ' x' → (θ = θ' ↔ x = x') ∧ ∀ l : ℕ, l.Prime → (CongrMod l θ θ' ↔ Formalism.CyclotomicNorms.primeToPart l x = Formalism.CyclotomicNorms.primeToPart l x') := by
  first | exact @GlobalTheory.ParamLabel.Congr.eq_and_congr | exact GlobalTheory.ParamLabel.Congr.eq_and_congr | (intros; apply GlobalTheory.ParamLabel.Congr.eq_and_congr <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelMoveLiftCongruentModIdeal
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.LevelMoveCong

open scoped TensorProduct

section Gen

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E]

theorem intAdele_smul_mem_hat {n : ℕ} (S : Set (Fin n → E)) (c : FiniteAdeleRing (𝓞 F) F)
    (hc : ∀ v, c v ∈ v.adicCompletionIntegers F) {z : Fin n → GlobalTheory.AdLat.RA F E}
    (hz : z ∈ GlobalTheory.AdLat.hat F S) : (c ⊗ₜ[F] (1 : E)) • z ∈ GlobalTheory.AdLat.hat F S := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨c * a, fun v => mul_mem (hc v) (ha v), x, hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem ideal_smul_mem_hat {n : ℕ} (I : Ideal (𝓞 E)) (L : Submodule (𝓞 E) (Fin n → E)) {t : 𝓞 E} (ht : t ∈ I)
    {z : Fin n → GlobalTheory.AdLat.RA F E} (hz : z ∈ GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) :
    ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (t : E)) • z ∈
      GlobalTheory.AdLat.hat F ((I • L : Submodule (𝓞 E) (Fin n → E)) : Set (Fin n → E)) := by
  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨a, ha, x, hx, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨a, ha, t • x, Submodule.smul_mem_smul ht hx, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
    rfl
  | zero => rw [smul_zero]; exact zero_mem _
  | add y y' _ _ h h' => rw [smul_add]; exact add_mem h h'
  | neg y _ h => rw [smul_neg]; exact neg_mem h

theorem nsmul_eq_smul {n : ℕ} (M : ℕ) (w : Fin n → GlobalTheory.AdLat.RA F E) :
    M • w = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (((M : 𝓞 E) : E))) • w := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, nsmul_eq_mul, map_natCast]
  rw [← Algebra.TensorProduct.includeRight_apply, map_natCast]

theorem split_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (x y : Fin n → GlobalTheory.AdLat.RA F E)
    (r : GlobalTheory.AdLat.RA F E) (h : x = y + r • x) :
    K *ᵥ x - x = (K *ᵥ y - y) + r • (K *ᵥ x - x) := by
  conv_lhs => rw [h]
  rw [Matrix.mulVec_add, Matrix.mulVec_smul, smul_sub]
  abel

theorem gen_sub {n : ℕ} (K : Matrix (Fin n) (Fin n) (GlobalTheory.AdLat.RA F E)) (c : FiniteAdeleRing (𝓞 F) F)
    (x : Fin n → E) :
    K *ᵥ (fun i => c ⊗ₜ[F] x i) - (fun i => c ⊗ₜ[F] x i) =
      (c ⊗ₜ[F] (1 : E)) • (K *ᵥ GlobalTheory.AdLat.fv F x - GlobalTheory.AdLat.fv F x) := by
  have e : (fun i => c ⊗ₜ[F] x i) = (c ⊗ₜ[F] (1 : E)) • GlobalTheory.AdLat.fv F x := by
    funext i; simp [GlobalTheory.AdLat.fv, Algebra.TensorProduct.tmul_mul_tmul]
  rw [e, Matrix.mulVec_smul, smul_sub]

end Gen

end GlobalTheory.LevelMoveCong

namespace GlobalTheory.LevelMoveCong

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.Pj
open scoped TensorProduct Matrix

set_option maxHeartbeats 2000000 in

theorem mulVec_sub_mem_hat_smul : ∀ {D : D7} (V : HSp D) {La : Type} [AddCommGroup La] [Module (𝓞 D.host.E) La] (ι : La →ₗ[𝓞 D.host.E] (Fin V.rank → D.host.E)), Formalism.L2.Pj.LatEmb V ι → ∀ (M : ℕ) (Mb Mh : Ideal (𝓞 D.host.E)), Mb ⊔ Mh = ⊤ → ((M : ℕ) : 𝓞 D.host.E) ∈ Mb → ∀ (κ : Formalism.L2.Theta.GA D V), GlobalTheory.Member.FinCong V 1 κ → ∀ (f : La →ₗ[𝓞 D.host.E] La), (∀ a ∈ Mh • (⊤ : Submodule (𝓞 D.host.E) La), ∃ w ∈ Formalism.L2.Pj.latGHat V 1, Formalism.L2.Pj.finVec V (ι (f a)) - (Formalism.L2.Theta.finHom V κ).1 *ᵥ Formalism.L2.Pj.finVec V (ι a) = M • w) → (∀ x, f x - x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La)) → ∀ z ∈ GlobalTheory.AdLat.hat D.host.F (Formalism.L2.Pj.latG V 1 : Set (Fin V.rank → D.host.E)), (Formalism.L2.Theta.finHom V κ).1 *ᵥ z - z ∈ GlobalTheory.AdLat.hat D.host.F ((Mb • Formalism.L2.Pj.latG V 1 : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) : Set (Fin V.rank → D.host.E)) := by
  intro D V La _ _ ι hι M Mb Mh hsup hM κ hκ f hf hfb z hz
  set K := (Formalism.L2.Theta.finHom V κ).1 with hKdef
  set L' := Formalism.L2.Pj.latG V 1 with hL'
  set P := GlobalTheory.AdLat.hat D.host.F ((Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) :
    Set (Fin V.rank → D.host.E)) with hP
  have hhat1 : Formalism.L2.Pj.latGHat V 1 = GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    (GlobalTheory.Member.latG_lattice_and_completion D V 1).2.2.2.2.1
  have hK : ∀ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)),
      K *ᵥ y ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) := by
    intro y hy
    have h4 := (GlobalTheory.Member.latG_lattice_and_completion D V κ).2.2.2.1
    have he := GlobalTheory.Member.LatMove.hat_eq_of_finCong V hκ
    have h5 : K *ᵥ y ∈ (Formalism.L2.Pj.latGHat V κ : Set _) := by rw [h4]; exact ⟨y, hy, rfl⟩
    rw [he, hhat1] at h5
    exact h5
  have hone : ∀ v, (1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) v ∈ v.adicCompletionIntegers D.host.F :=
    fun v => one_mem _
  have hfv : ∀ u ∈ L', Formalism.L2.Pj.finVec V u ∈ GlobalTheory.AdLat.hat D.host.F (L' : Set (Fin V.rank → D.host.E)) :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  have hfvP : ∀ u ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)), Formalism.L2.Pj.finVec V u ∈ P :=
    fun u hu => AddSubgroup.subset_closure ⟨1, hone, u, hu, rfl⟩
  obtain ⟨b, hb, m, hm, hmb⟩ : ∃ b ∈ Mb, ∃ m ∈ Mh, b + m = 1 :=
    Submodule.mem_sup.1 (hsup ▸ Submodule.mem_top)
  have hfv_sub : ∀ u u', Formalism.L2.Pj.finVec V (u - u') = Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u' := by
    intro u u'; funext i; simp [Formalism.L2.Pj.finVec, TensorProduct.tmul_sub]
  have hrange : ∀ x ∈ Mb • (⊤ : Submodule (𝓞 D.host.E) La),
      ι x ∈ (Mb • L' : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) := by
    intro x hx
    have h1 : ι x ∈ (Mb • (⊤ : Submodule (𝓞 D.host.E) La)).map ι := Submodule.mem_map_of_mem hx
    rwa [Submodule.map_smul'', Submodule.map_top, hι.2] at h1

  have step1 : ∀ v : La, K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) ∈ P := by
    intro v
    obtain ⟨w, hw, hw'⟩ := hf (m • v) (Submodule.smul_mem_smul hm Submodule.mem_top)
    have e : K *ᵥ Formalism.L2.Pj.finVec V (ι (m • v)) - Formalism.L2.Pj.finVec V (ι (m • v)) =
        Formalism.L2.Pj.finVec V (ι (f (m • v) - m • v)) - M • w := by
      rw [map_sub, hfv_sub, ← hw']; abel
    rw [e]
    refine sub_mem (hfvP _ (hrange _ (hfb _))) ?_
    rw [hhat1] at hw
    rw [nsmul_eq_smul]
    exact ideal_smul_mem_hat Mb L' hM hw

  have step2 : ∀ u ∈ L', K *ᵥ Formalism.L2.Pj.finVec V u - Formalism.L2.Pj.finVec V u ∈ P := by
    intro u hu
    have hu' : u ∈ LinearMap.range ι := by rw [hι.2]; exact hu
    obtain ⟨v, rfl⟩ := hu'
    have hsplit : Formalism.L2.Pj.finVec V (ι v) = Formalism.L2.Pj.finVec V (ι (m • v)) +
        ((1 : FiniteAdeleRing (𝓞 D.host.F) D.host.F) ⊗ₜ[D.host.F] ((b : 𝓞 D.host.E) : D.host.E)) •
          Formalism.L2.Pj.finVec V (ι v) := by
      funext i
      simp only [Formalism.L2.Pj.finVec, map_smul, Pi.add_apply, Pi.smul_apply, smul_eq_mul,
        Algebra.TensorProduct.tmul_mul_tmul, one_mul]
      rw [← TensorProduct.tmul_add]
      congr 1
      rw [Algebra.smul_def, ← add_mul]
      have : ((algebraMap (𝓞 D.host.E) D.host.E m) + (b : D.host.E)) = 1 := by
        show ((m : D.host.E)) + (b : D.host.E) = 1
        rw [add_comm]; exact_mod_cast congrArg ((↑) : 𝓞 D.host.E → D.host.E) hmb
      rw [this, one_mul]
    rw [split_sub K _ _ _ hsplit]
    refine add_mem (step1 v) (ideal_smul_mem_hat Mb L' hb ?_)
    have hu : ι v ∈ L' := by rw [hL', ← hι.2]; exact ⟨v, rfl⟩
    exact sub_mem (hK _ (hfv _ hu)) (hfv _ hu)

  induction hz using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨c, hc, x, hx, rfl⟩ := hy
    rw [gen_sub K c x]
    exact intAdele_smul_mem_hat _ c hc (step2 x hx)
  | zero => rw [Matrix.mulVec_zero, sub_zero]; exact zero_mem _
  | add y y' _ _ h h' =>
    have e : K *ᵥ (y + y') - (y + y') = (K *ᵥ y - y) + (K *ᵥ y' - y') := by
      rw [Matrix.mulVec_add]; abel
    rw [e]; exact add_mem h h'
  | neg y _ h =>
    have e : K *ᵥ (-y) - (-y) = -(K *ᵥ y - y) := by
      rw [Matrix.mulVec_neg]; abel
    rw [e]; exact neg_mem h

end GlobalTheory.LevelMoveCong
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieConditionOfComplexExpIntertwinesActionStatement
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.PELU
open scoped Matrix
open GlobalTheory.UPel.HT
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lieCondition_of_complexExp_intertwines_action : ∀ (p : ℕ) [Fact p.Prime] (D : Datum p) (R : Type) [CommRing R] (b : Base D R) (N : ℕ) (σ : R →+* ℂ) (ρ : D.O →+* Matrix (Fin D.g) (Fin D.g) ℂ) (A : Over (Sp ℂ)) [GrpObj A] [IsCommMonObj A] (act : OActN D.O A) (e : (Fin D.g → ℂ) → (Over.mk (𝟙 (Sp ℂ)) ⟶ A)), IsAbelianScheme A → SmoothOfRelativeDimension D.g A.hom → IsExp (𝟙 (Sp ℂ)) e → (∀ a z, e (ρ a *ᵥ z) = e z ≫ act.act a) → b.IsType σ ρ → (∀ (R' : Type) [CommRing R'] (β : R →+* R') (x : Sp R' ⟶ Sp ℂ), x ≫ spMap σ = spMap β → ∀ v : epsPtR x ⟶ A, IsTanScal act x (algebraMap (𝓞 D.F) D.O D.ω) (β b.ρ) v → ∃ w : Fin D.a → (epsPtR x ⟶ A), (∀ i, ∀ c : 𝓞 D.F, IsTanScal act x (algebraMap (𝓞 D.F) D.O c) (β (b.t i c)) (w i)) ∧ v = (List.ofFn w).prod) ∧ ∀ (k : Type) [Field k] [IsAlgClosed k] (x : Sp k ⟶ Sp ℂ) (β : R →+* k), x ≫ spMap σ = spMap β → ∀ i, LieMult (act.toF D) x (β.comp (b.t i)) D.m := by
  first | exact @GlobalTheory.UPel.HT.lie_of_complexExp | exact GlobalTheory.UPel.HT.lie_of_complexExp | (intros; apply GlobalTheory.UPel.HT.lie_of_complexExp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftMemLevelOfDatumFlagCharacterStatement
section
open NumberField IsDedekindDomain MeasureTheory Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Lev Formalism.IndefR.Datum Formalism.IndefR
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lift_mem_levelOfDatum_flagCharacter : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T : Type} {A : FamIn D.what₂.LL G Pl0 T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), ∀ (i : Fin D.R.m) (t : T) (P : LevelP R.Pg D.R.r ℂ) (g0 : P.H) (κ : GA D (Vc D i)), IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) g0.1 κ → κ ∈ levG (Vc D i) (R.βV i) (RecTie.datVP R i t P) ∧ levChi (Vc D i) (R.βV i) (RecTie.datVP R i t P) κ = ((P.chi g0 : ℂˣ) : ℂ)⁻¹ * levChi (Vc D i) (R.βV i) (flagL (R.datVt i t)) κ := by
  first | exact @GlobalTheory.lift_mem_levVP | exact GlobalTheory.lift_mem_levVP | (intros; apply GlobalTheory.lift_mem_levVP <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionIntegralPointOfStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionIntegralPoint_of_steps : AddSt → ActSt → ContSt → LimPtSt := by
  first | exact @GlobalTheory.IsoTriv.limPt_of_steps | exact GlobalTheory.IsoTriv.limPt_of_steps | (intros; apply GlobalTheory.IsoTriv.limPt_of_steps <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitActionLieAlgebraOfPrimeIdempotentApproxStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitActionLieAlgebra_of_primeIdempotentApprox : EpsSt → LimActSt := by
  first | exact @GlobalTheory.IsoTriv.limActSt_of_epsSt | exact GlobalTheory.IsoTriv.limActSt_of_epsSt | (intros; apply GlobalTheory.IsoTriv.limActSt_of_epsSt <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LimitIsotropicFrameIntegralOfStepsStatement
section
open GlobalTheory.IsoTriv
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.limitIsotropicFrameIntegral_of_steps : AddSt → ActSt → UnitSt → BiaddSt → FrameSt → FinSt → ContSt → LimFrameSt := by
  first | exact @GlobalTheory.IsoTriv.limFrame | exact GlobalTheory.IsoTriv.limFrame | (intros; apply GlobalTheory.IsoTriv.limFrame <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleOnOpenPullCompIsoStatement
section
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual GlobalTheory.DualCon GlobalTheory.PicGlue Opposite
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lineBundleOnOpen_pull_comp_iso : ∀ (X Z Z' : Scheme.{0}) (W : X.Opens) (L : LB X) (r : Z ⟶ X) (s : Z' ⟶ Z), IsOn W L → (∀ z, r z ∈ W) → LBIso ((L.pull r).pull s) (L.pull (s ≫ r)) := by
  first | exact @GlobalTheory.PicGlue.isOn_pull_comp | exact GlobalTheory.PicGlue.isOn_pull_comp | (intros; apply GlobalTheory.PicGlue.isOn_pull_comp <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LineBundleSectionsProductBaseChange
section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.EndLoc
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G.Out
open GlobalTheory.HomFixMat

noncomputable section

namespace GlobalTheory.HomFixMatEx

theorem liftTop (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg)
    (A' : Over (Sp R)) (φA' : A'.left ⟶ A.left) (hpb : IsPullback φA' A'.hom A.hom t) :
    ∃ ψ : A'.left ⟶ (topS Rg ⊗ A).left, ψ ≫ (snd (topS Rg) A).left = φA' := by
  let a0 : A'.left ⟶ (⊤ : (Sp Rg).Opens).toScheme :=
    IsOpenImmersion.lift (⊤ : (Sp Rg).Opens).ι (A'.hom ≫ t) (by simp)
  let X : Over (Sp Rg) := Over.mk (A'.hom ≫ t)
  let a : X ⟶ topS Rg := Over.homMk a0 (by simp only [a0, X, topS, overRes, baseOver, Over.mk_hom, Category.comp_id]; exact IsOpenImmersion.lift_fac _ _ _)
  let b : X ⟶ A := Over.homMk φA' hpb.w
  refine ⟨(lift a b).left, ?_⟩
  rw [← Over.comp_left, lift_snd]
  rfl

theorem zero_comp (Rg : Type) [CommRing Rg] (A : Over (Sp Rg)) [GrpObj A] (R : Type) [CommRing R]
    (t : Sp R ⟶ Sp Rg) (A' : Over (Sp R)) [GrpObj A'] (φA' : A'.left ⟶ A.left) (h : IsGrpPullback A' A t φA') :
    zeroPt A' ≫ φA' = t ≫ eSec A := by
  let T : Over (Sp R) := 𝟙_ (Over (Sp R))
  let u : Over.mk (T.hom ≫ t) ⟶ A := Over.homMk ((1 : T ⟶ A').left ≫ φA') (by
    simp only [Over.mk_hom, Category.assoc]
    rw [h.1.w, ← Category.assoc, Over.w])
  have hu : u * u = u := Over.OverMorphism.ext (by
    rw [h.2 T 1 1 u u rfl rfl, _root_.mul_one]; rfl)
  have hu1 : u = 1 := mul_eq_left.1 hu
  have e := congrArg (fun x => Over.Hom.left x) hu1
  simp only [u, Over.homMk_left] at e
  rw [Hom.one_def, Hom.one_def] at e
  simp at e
  exact e
end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMatEx

theorem res_appLE {X Y : Scheme.{0}} (f : X ⟶ Y) {U : Y.Opens} {V V' : X.Opens} (e : V ≤ f ⁻¹ᵁ U) (h : V' ≤ V)
    (x : Γ(Y, U)) :
    (X.presheaf.map (homOfLE h).op).hom ((f.appLE U V e).hom x) = (f.appLE U V' (h.trans e)).hom x := by
  rw [← CommRingCat.comp_apply, Scheme.Hom.appLE_map]

end GlobalTheory.HomFixMatEx

namespace GlobalTheory.HomFixMat
open GlobalTheory.HomFixMatEx

theorem exists_isMat : ∀ (Rg : Type) [CommRing Rg] [IsNoetherianRing Rg] (A B : Over (Sp Rg)) [GrpObj A] [IsCommMonObj A] [GrpObj B] [IsCommMonObj B] (L : LB A.left) (M : LB B.left) (k : ℕ) (mA mB : ℕ) (bA : Fin mA → LB.Sec (LPow A L (k : ℤ) (topS Rg))) (bB : Fin mB → LB.Sec (LPow B M (k : ℤ) (topS Rg))) (eA : LB.Gen (L.pull (eSec A))) (eB : LB.Gen (M.pull (eSec B))), Hyps L M k bA bB eA eB → ∀ (R : Type) [CommRing R] (t : Sp R ⟶ Sp Rg) (A' B' : Over (Sp R)) [GrpObj A'] [GrpObj B'] (φA' : A'.left ⟶ A.left) (φB' : B'.left ⟶ B.left) (Φ' : A' ⟶ B'), IsTest A B L M t A' B' φA' φB' Φ' → ∃ c, IsMat L M k bA bB eA eB t A' B' φA' φB' Φ' c := by
  intro Rg _ _ A B _ _ _ _ L M k mA mB bA bB eA eB hH R _ t A' B' _ _ φA' φB' Φ' hT
  obtain ⟨_, _, hL, hM, heA, heB, _, _, _, hbA, _⟩ := hH
  obtain ⟨hpA, hpB, hΦ, hiso⟩ := hT
  obtain ⟨ψA, hψA⟩ := liftTop Rg A R t A' φA' hpA.1
  obtain ⟨ψB, hψB⟩ := liftTop Rg B R t B' φB' hpB.1
  obtain ⟨w, hw⟩ := hiso
  have eg : (Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left = Φ'.left ≫ φB' := by rw [Category.assoc, hψB]
  obtain ⟨α₀, hα₀⟩ : ∃ α₀ : LB.Gen (isoLB (L := L) (M := M) k Φ' ψA ψB), α₀.IsGen := by
    have := GlobalTheory.T.exists_lineBundlePower_iso_reindexed_charts L M φA' Φ'.left φB' k w hw
    show ∃ α₀ : LB.Gen (LB.div (powPull M ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (k : ℤ))
      (powPull L (ψA ≫ (snd (topS Rg) A).left) (k : ℤ))), α₀.IsGen
    rw [eg, hψA]; exact this
  have hΦ0 : zeroPt A' ≫ Φ'.left = zeroPt B' := by
    haveI := hΦ
    exact congrArg Over.Hom.left (IsMonHom.one_hom (f := Φ'))
  have hz1 : zeroPt A' ≫ (ψA ≫ (snd (topS Rg) A).left) = t ≫ eSec A := by
    rw [hψA]; exact zero_comp Rg A R t A' φA' hpA
  have hz2 : zeroPt A' ≫ ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) = t ≫ eSec B := by
    rw [eg, ← Category.assoc, hΦ0]; exact zero_comp Rg B R t B' φB' hpB
  have hzπ : zeroPt A' ≫ A'.hom = 𝟙 (Sp R) := Over.w η[A']
  obtain ⟨α, hα, hrig⟩ := GlobalTheory.T.exists_rescaled_lineBundlePower_iso_generator (Z₀ := Sp Rg) L M (ψA ≫ (snd (topS Rg) A).left)
    ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left) (eSec A) (eSec B) t (zeroPt A') A'.hom k eA eB α₀
    hL hM heA heB hα₀ hzπ hz1 hz2
  have key : ∀ j : Fin mB, ∃ cj : Fin mA → Γ(Sp R, ⊤), ∀ p : (Fin 1 → M.ι) × (Fin 1 → L.ι),
      ((Φ'.left ≫ ψB).appLE (LB.wchart M (fun _ : Fin 1 => (snd (topS Rg) B).left) p.1)
          ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
          (inf_le_left.trans (GlobalTheory.HomFixMat.wchart_comp_le M _ _ p.1))).hom ((bB j).f p.1) =
        (α.s p).val * ∑ i, (A'.hom.appLE ⊤ ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p) (by simp)).hom (cj i) *
          (ψA.appLE (LB.wchart L (fun _ : Fin 1 => (snd (topS Rg) A).left) p.2)
            ((isoLB (L := L) (M := M) k Φ' ψA ψB).U p)
            (inf_le_right.trans (GlobalTheory.HomFixMat.wchart_comp_le L _ _ p.2))).hom ((bA i).f p.2) := by
    intro j
    obtain ⟨σ, hσ⟩ := GlobalTheory.T.exists_lineBundlePowerPullback_section_pullback M (snd (topS Rg) B).left (Φ'.left ≫ ψB) (k : ℤ) (bB j)
    obtain ⟨s, hs⟩ := GlobalTheory.T.power_pullback_section_exists L M (ψA ≫ (snd (topS Rg) A).left) ((Φ'.left ≫ ψB) ≫ (snd (topS Rg) B).left)
      (k : ℤ) α hα hL hM σ
    obtain ⟨c, hc⟩ := GlobalTheory.T.exists_coeff_pullback_baseChangeStableSectionBasis Rg A L k mA bA hbA R t A' φA' hpA.1 ψA hψA s
    refine ⟨c, fun p => ?_⟩
    have e1 := hs p
    rw [hσ p.1, hc p.2, map_sum] at e1
    erw [res_appLE] at e1
    simp only [map_mul] at e1
    erw [e1]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    congr 1
    · exact res_appLE _ _ _ _
    · exact res_appLE _ _ _ _
  choose cj hcj using key
  exact ⟨fun i j => cj j i, ψA, ψB, α, hψA, hψB, hα, hrig, fun j p => hcj j p⟩

end GlobalTheory.HomFixMat
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCutOperatorTransferAdelicWhittakerStatement
section
open NumberField IsDedekindDomain GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun Matrix MeasureTheory
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.localCutOperator_transfer_adelicWhittaker : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (w : HeightOneSpectrum (𝓞 E)) (ψ : AddChar (w.adicCompletion E) ℂ), (∀ x, ψ x = GlobalTheory.JSW.psiLoc w x) → ∀ (K : Subgroup (GL (Fin (m + 1)) (Af E))) (U : Subgroup (GL (Fin (m + 1)) (w.adicCompletion E))), (∀ u ∈ U, locGL E (m + 1) w u ∈ K) → ∀ X A : Set (GL (Fin (m + 1)) (w.adicCompletion E)), GlobalTheory.JSW.Cut.Cuts ψ (U : Set (GL (Fin (m + 1)) (w.adicCompletion E))) X A → ∃ T : GA E (m + 1) →₀ ℂ, (∀ k ∈ T.support, ∃ g, k = finGL E (m + 1) (locGL E (m + 1) w g)) ∧ ∀ W : GA E (m + 1) → ℂ, (∀ u ∈ GlobalTheory.JSW.NA E (m + 1), ∀ g, W (u * g) = GlobalTheory.JSW.psiN u * W g) → (∀ u ∈ K, ∀ g, W (g * finGL E (m + 1) u) = W g) → ∀ y : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) y ∈ A → GlobalTheory.JSW.Cut.act T W y = {x : GA E (m + 1) | GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) x ∈ X}.indicator W y := by
  first | (exact @GlobalTheory.JSW.CutTransfer.transfer) | (exact GlobalTheory.JSW.CutTransfer.transfer) | (intros; apply GlobalTheory.JSW.CutTransfer.transfer  <;> assumption)
end

