import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.NonemptyEquivMultiProdOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0643
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.RatDatOfReal
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnipotentBlockColumnIndex
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0011
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0103
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0086
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0142
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0013
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AutomorphicArithmetic.ResidueCharacters.TwistedPlaces
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRhoPtOfSplitting
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0006
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWeilDatumOOneOfRankZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEqColGenMulBlkU
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0006
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0003
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0020
import GroundTheory.GlobalFields.TateThesis.Bundle0007

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem
section
noncomputable section

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix
open GlobalTheory.Parabolic (mem_fixed)

namespace GlobalTheory.LocGL

section FiniteGroup

variable {G V W X Y : Type} [Group G] [Fintype G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] [AddCommGroup Y] [Module ℂ Y] [FiniteDimensional ℂ W]

theorem charIdem_apply (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v =
      ((Module.finrank ℂ W : ℂ) / Fintype.card G) • ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v := by
  simp [charIdem, LinearMap.sum_apply]

theorem map_charIdem {σ : Representation ℂ G V} {σ' : Representation ℂ G X} (φ : σ.IntertwiningMap σ')
    (τ : Representation ℂ G W) (v : V) : φ (charIdem σ τ v) = charIdem σ' τ (φ v) := by
  simp only [charIdem_apply, map_smul, map_sum, φ.isIntertwining]

theorem charIdem_apply_rep (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) (v : V) :
    charIdem σ τ (σ h v) = σ h (charIdem σ τ v) := by
  simp only [charIdem_apply, map_smul, map_sum]
  congr 1
  refine (Fintype.sum_equiv (MulAut.conj h).toEquiv _ _ fun g => ?_).symm
  have e : LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) = LinearMap.trace ℂ W (τ g⁻¹) := by
    rw [show (h * g * h⁻¹)⁻¹ = h * g⁻¹ * h⁻¹ by group]
    exact τ.char_conj g⁻¹ h
  show _ = LinearMap.trace ℂ W (τ (h * g * h⁻¹)⁻¹) • σ (h * g * h⁻¹) (σ h v)
  rw [e, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, inv_mul_cancel_right]

theorem commute_charIdem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (h : G) :
    Commute (charIdem σ τ) (σ h) := LinearMap.ext (charIdem_apply_rep σ τ h)

def coeffMap (σ : Representation ℂ G V) (τ : Representation ℂ G W) (ℓ : Module.Dual ℂ W) (v : V) :
    τ.IntertwiningMap σ where
  toLinearMap := ∑ g : G, (ℓ ∘ₗ τ g⁻¹).smulRight (σ g v)
  isIntertwining' h := LinearMap.ext fun w => by
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smulRight_apply, map_sum, map_smul]
    refine (Fintype.sum_equiv (Equiv.mulLeft h) _ _ fun g => ?_).symm
    simp only [Equiv.coe_mulLeft, ← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, inv_mul_cancel_right]

theorem charIdem_mem (σ : Representation ℂ G V) (τ : Representation ℂ G W) (v : V) :
    charIdem σ τ v ∈ isotypic σ τ := by
  classical
  let b := Module.finBasis ℂ W
  have key : ∑ g : G, LinearMap.trace ℂ W (τ g⁻¹) • σ g v = ∑ i, coeffMap σ τ (b.coord i) v (b i) := by
    have : ∀ i, coeffMap σ τ (b.coord i) v (b i) = ∑ g : G, b.repr (τ g⁻¹ (b i)) i • σ g v := fun i => by
      show (∑ g : G, (b.coord i ∘ₗ τ g⁻¹).smulRight (σ g v)) (b i) = _
      simp [LinearMap.sum_apply]
    simp only [this]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [← Finset.sum_smul, LinearMap.trace_eq_matrix_trace ℂ b]
    simp [Matrix.trace, LinearMap.toMatrix_apply]
  rw [charIdem_apply, key]
  exact (isotypic σ τ).toSubmodule.smul_mem _ (Submodule.sum_mem _ fun i _ => apply_mem_isotypic _ _)

theorem charIdem_self {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) : charIdem τ τ = 1 := by
  have := Model.nontrivial_of_isIrreducible hτ
  obtain ⟨c, hc⟩ := (Representation.IsIrreducible.algebraMap_intertwiningMap_bijective_of_isAlgClosed (ρ := τ)).2
    ⟨charIdem τ τ, fun g => commute_charIdem τ τ g⟩
  have h1 : charIdem τ τ = c • (1 : Module.End ℂ W) :=
    LinearMap.ext fun w => (congrArg (fun f : τ.IntertwiningMap τ => f w) hc).symm
  haveI : Invertible (Nat.card G : ℂ) := invertibleOfNonzero (Nat.cast_ne_zero.2 Nat.card_pos.ne')
  have ho := Representation.char_orthonormal τ τ
  rw [if_pos ⟨.refl _⟩, Nat.card_eq_fintype_card] at ho
  have hd : (Module.finrank ℂ W : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Module.finrank_pos.ne'
  have h2 : LinearMap.trace ℂ W (charIdem τ τ) = Module.finrank ℂ W := by
    simp only [charIdem, map_smul, map_sum, smul_eq_mul]
    rw [div_eq_mul_inv, mul_assoc]
    refine (congrArg _ (Eq.trans ?_ ho)).trans (mul_one _)
    exact congrArg _ (Finset.sum_congr rfl fun g _ => mul_comm _ _)
  rw [h1, map_smul, LinearMap.trace_one, smul_eq_mul] at h2
  rw [h1, mul_right_cancel₀ hd (h2.trans (one_mul _).symm), one_smul]

theorem charIdem_of_mem {σ : Representation ℂ G V} {τ : Representation ℂ G W} (hτ : τ.IsIrreducible) {v : V}
    (hv : v ∈ isotypic σ τ) : charIdem σ τ v = v := by
  refine Submodule.iSup_induction _ (motive := fun v => charIdem σ τ v = v) hv ?_ (map_zero _) fun x y hx hy => ?_
  · rintro f _ ⟨w, rfl⟩
    exact (map_charIdem f τ w).symm.trans (by rw [charIdem_self hτ]; rfl)
  · rw [map_add, hx, hy]

end FiniteGroup

section Compact

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {π : Representation ℂ G V} {σ : Representation ℂ G W} {H : Subgroup G}

theorem map_idem (hπ : IsSmooth π) (hσ : IsSmooth σ) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) (v : V) :
    f (idem hπ hH v) = idem hσ hH (f v) := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  rw [idem_eq_cosetSum hπ hH U hU, idem_eq_cosetSum hσ hH U fun u hu => by rw [← f.isIntertwining, hU u hu]]
  simp only [map_smul, map_sum, f.isIntertwining]

theorem map_idem_of_mem (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : f (idem hπ hH v) = f v := by
  obtain ⟨U, -, _, hU⟩ := exists_normal_fix hπ hH v
  letI := Fintype.ofFinite (H ⧸ U)
  have hc : (Fintype.card (H ⧸ U) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  rw [idem_eq_cosetSum hπ hH U hU]
  simp only [map_smul, map_sum, f.isIntertwining]
  rw [Finset.sum_congr rfl fun q _ => mem_fixed.1 hv _ (q.out : H).2, Finset.sum_const, Finset.card_univ,
    ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]

theorem exists_mem_fixed_map_eq (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) (f : π.IntertwiningMap σ) {v : V}
    (hv : f v ∈ fixed σ H) : ∃ u ∈ fixed π H, f u = f v :=
  ⟨_, idem_mem hπ hH v, map_idem_of_mem hπ hH f hv⟩

theorem map_fixed_of_surjective (hπ : IsSmooth π) (hH : IsCompact (H : Set G)) {f : π.IntertwiningMap σ}
    (hf : Function.Surjective f) : (fixed π H).map f.toLinearMap = fixed σ H := by
  refine le_antisymm ?_ fun w hw => ?_
  · rintro _ ⟨v, hv, rfl⟩
    exact mem_fixed.2 fun u hu => by rw [f.toLinearMap_apply, ← f.isIntertwining, mem_fixed.1 hv u hu]
  · obtain ⟨v, rfl⟩ := hf w
    exact exists_mem_fixed_map_eq hπ hH f hw

end Compact

section LevelZero

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type} [Fintype n] [DecidableEq n] {V W X : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]
  [AddCommGroup X] [Module ℂ X] {π : Representation ℂ (GL n k) V} {σ : Representation ℂ (GL n k) W}
  {ρ : Representation ℂ (GL n k) X}

@[simp] theorem levelZeroMap_apply (f : π.IntertwiningMap σ) (v : fixed π (KOne k n)) :
    (levelZeroMap f v : W) = f v := rfl

theorem levelZeroMap_injective {f : π.IntertwiningMap σ} (hf : Function.Injective f) :
    Function.Injective (levelZeroMap f) :=
  fun _ _ h => Subtype.ext (hf (congrArg Subtype.val h))

theorem levelZeroMap_surjective (hπ : IsSmooth π) {f : π.IntertwiningMap σ} (hf : Function.Surjective f) :
    Function.Surjective (levelZeroMap f) := by
  rintro ⟨x, hx⟩
  obtain ⟨v, rfl⟩ := hf x
  obtain ⟨u, hu, h⟩ := exists_mem_fixed_map_eq hπ (levelPre_bot (k := k) (n := n) ▸ isCompact_levelPre ⊥) f hx
  exact ⟨⟨u, hu⟩, Subtype.ext h⟩

end LevelZero

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsKsFormOfAlgebraicFormsIsoStatement
section
open NumberField Formalism.IndefR.NX
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isKsForm_of_algebraicFormsIso : ∀ {LL Ks Ks' WL WL' G G' : Type} [Field LL] [NumberField LL] [Field Ks] [NumberField Ks]
    [Algebra Ks LL] [Field Ks'] [NumberField Ks'] [Algebra Ks' LL] [AddCommGroup WL] [Module LL WL] [Module Ks WL]
    [IsScalarTower Ks LL WL] [Module (𝓞 Ks) WL] [IsScalarTower (𝓞 Ks) Ks WL] [AddCommGroup WL'] [Module LL WL']
    [Module Ks' WL'] [IsScalarTower Ks' LL WL'] [Module (𝓞 Ks') WL'] [IsScalarTower (𝓞 Ks') Ks' WL']
    {W W' : (LL →+* ℂ) → Type} [∀ σ, NormedAddCommGroup (W σ)] [∀ σ, InnerProductSpace ℂ (W σ)]
    [∀ σ, NormedAddCommGroup (W' σ)] [∀ σ, InnerProductSpace ℂ (W' σ)] [Group G] [Group G']
    (A : Formalism.IndefR.Arith.FormsL LL Ks WL W G) (A' : Formalism.IndefR.Arith.FormsL LL Ks' WL' W' G'),
    FormsIso A A' → A'.IsKsForm → A.IsKsForm := by
  first | exact @GlobalTheory.isKsForm_of_formsIso | exact GlobalTheory.isKsForm_of_formsIso | (intros; apply GlobalTheory.isKsForm_of_formsIso <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsMirabolicWhittakerStageOfIsCuspFormStatement
section
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.CuspGeneric
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.isMirabolicWhittakerStage_of_isCuspForm : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (a : ℕ) (ψ : AddChar (Ad E) ℂ) (φ : Sm E a), IsCuspForm φ → Good ψ (a - 1) φ.1 := by
  first | exact @GlobalTheory.CuspGeneric.good_of_isCuspForm | exact GlobalTheory.CuspGeneric.good_of_isCuspForm | (intros; apply GlobalTheory.CuspGeneric.good_of_isCuspForm <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsPotentiallySemistableOfSemistableRestrict
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

theorem isPst_resTo_iff_padic {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K K' : FinExt l} (hK : K.1 ≤ K'.1)
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V) :
    IsPst P (resTo ρ hK) ↔ IsPst P ρ := by
  let e : DpstUr P (resTo ρ hK) ≃ₗ[↥(MaximalUnramifiedExtension l)] DpstUr P ρ :=
    { toFun := fun x =>
        toUr P ρ ⟨((toUr P _).symm x).1, (Dpst_resTo P ρ hK).le ((toUr P _).symm x).2⟩
      invFun := fun x =>
        toUr P _ ⟨((toUr P ρ).symm x).1, (Dpst_resTo P ρ hK).ge ((toUr P ρ).symm x).2⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [IsPst, IsPst, e.rank_eq]

theorem finrank_le_finrank_DpstUr_of_isSst {l : ℕ} [Fact l.Prime] (P : LocPrime l) {K : FinExt l}
    {V : Type} [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V]
    (ρ : Representation ℚ_[l] ↥(GK K) V) [FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P ρ)] (hS : IsSst P ρ) :
    finrank ℚ_[l] V ≤ finrank ↥(MaximalUnramifiedExtension l) (DpstUr P ρ) := by
  haveI := K.2
  haveI : FiniteDimensional ℚ_[l] ↥(K0 K) :=
    FiniteDimensional.of_injective (IntermediateField.inclusion (inf_le_left : K0 K ≤ K.1)).toLinearMap
      (IntermediateField.inclusion_injective inf_le_left)
  let val : DpstUr P ρ →+ V ⊗[ℚ_[l]] Bst P :=
    (Dpst P ρ).subtype.toAddMonoidHom.comp (toUr P ρ).symm.toAddMonoidHom
  have hSD : Dst P ρ ≤ Dpst P ρ := fun s hs => (mem_Dpst P ρ).mpr ⟨K, fun g _ => (mem_Dst P ρ).mp hs g⟩
  obtain ⟨b, hbS, hsp, hli⟩ := exists_linearIndependent ↥(MaximalUnramifiedExtension l) {y : DpstUr P ρ | val y ∈ Dst P ρ}
  haveI : Finite ↥b := hli.finite
  letI : Fintype ↥b := Fintype.ofFinite _
  have hspan : ∀ y : DpstUr P ρ, y ∈ Submodule.span ↥(MaximalUnramifiedExtension l) b → ∃ c : ↥b → ↥(MaximalUnramifiedExtension l),
      ∑ i, c i • (i : DpstUr P ρ) = y := fun y hy => by
    rw [← Submodule.mem_span_range_iff_exists_fun, Subtype.range_coe]; exact hy
  let inc : ↥(K0 K) →ₐ[ℚ_[l]] ↥(MaximalUnramifiedExtension l) := IntermediateField.inclusion (inf_le_right : K0 K ≤ MaximalUnramifiedExtension l)
  let f : (↥b → ↥(K0 K)) →ₗ[ℚ_[l]] V ⊗[ℚ_[l]] Bst P :=
    { toFun := fun c => ∑ i, mulV P ℚ_[l] V (inc (c i)) (val i)
      map_add' := fun c c' => by simp [Finset.sum_add_distrib]
      map_smul' := fun q c => by
        simp only [Pi.smul_apply, RingHom.id_apply, Finset.smul_sum]
        exact Finset.sum_congr rfl fun i _ => mulV_padic_smul P _ V q (inc (c i)) (val i) }
  have hle : Dst P ρ ≤ LinearMap.range f := by
    intro s hs
    obtain ⟨c, hc⟩ := hspan (toUr P ρ ⟨s, hSD hs⟩) (hsp ▸ Submodule.subset_span hs)
    have hfix : ∀ i, (c i : Om l) ∈ K.1 := fun i => mem_of_GK_fixed fun g => by
      have := semilinear_coord_fixed hli (fun a => ⟨_, galois_mem_Kur g a⟩)
        (actD P ρ g).toAddMonoidHom
        (fun a y => LinearMap.congr_fun (actD_mulD P ρ g a _ rfl) y)
        (fun j => Subtype.ext ((mem_Dst P ρ).mp (hbS j.2) g)) c
        (by rw [hc]; exact Subtype.ext ((mem_Dst P ρ).mp hs g)) i
      exact congrArg Subtype.val this
    refine ⟨fun i => ⟨c i, hfix i, (c i).2⟩, ?_⟩
    have := congrArg val hc
    rw [map_sum] at this
    exact this
  have h1 : finrank ℚ_[l] ↥(Dst P ρ) ≤ Fintype.card ↥b * finrank ℚ_[l] ↥(K0 K) := by
    refine (Submodule.finrank_mono hle).trans ((LinearMap.finrank_range_le f).trans ?_)
    simp [Module.finrank_pi_fintype]
  have h2 : finrank ℚ_[l] ↥(Dst P ρ) = finrank ℚ_[l] V * finrank ℚ_[l] ↥(K0 K) := by
    rw [show finrank ℚ_[l] ↥(Dst P ρ) = _ from hS, mul_comm]
  have h3 : finrank ℚ_[l] V ≤ Fintype.card ↥b :=
    Nat.le_of_mul_le_mul_right (h2 ▸ h1) Module.finrank_pos
  exact h3.trans hli.fintype_card_le_finrank

theorem isPst_of_isSst_resTo : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P) (T : LocTied l P AI) (K K' : FinExt l) (hK : K.1 ≤ K'.1) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] [FiniteDimensional ℚ_[l] V] (ρ : Representation ℚ_[l] ↥(GK K) V), IsSst P (resTo ρ hK) → IsPst P ρ := by
  intro l _ P AI T K K' hK V _ _ _ ρ hS
  obtain ⟨hdom, hreg, -⟩ := GlobalTheory.Pst.stRegular l P AI ⟨T⟩
  have hup := GlobalTheory.PstRank.rank_DpstUr_le P hdom hreg (resTo ρ hK)
  haveI : FiniteDimensional ↥(MaximalUnramifiedExtension l) (DpstUr P (resTo ρ hK)) :=
    Module.rank_lt_aleph0_iff.mp (hup.trans_lt (Cardinal.nat_lt_aleph0 _))
  rw [← isPst_resTo_iff_padic P hK ρ, GlobalTheory.Pst.isPst_iff]
  refine ⟨inferInstance, le_antisymm ?_ (finrank_le_finrank_DpstUr_of_isSst P _ hS)⟩
  rw [← finrank_eq_rank] at hup
  exact_mod_cast hup

end GlobalTheory.PMon

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSupercuspidalCompGeneralLinearGroupMapOfFieldE
section
noncomputable section

open Matrix GlobalTheory.SmGL GlobalTheory.PRep

namespace GlobalTheory.LocGL

section Rad

variable {R S : Type} [CommRing R] [CommRing S] {α n : Type} {m : α → Type} [Fintype α] [LinearOrder α]
  [∀ a, Fintype (m a)] [∀ a, DecidableEq (m a)] [Fintype n] [DecidableEq n]

theorem map_mem_unipRad_of_ringHom (f : R →+* S) {e : (Σ a, m a) ≃ n} {g : GL n R} (hg : g ∈ unipRad R e) :
    GeneralLinearGroup.map f g ∈ unipRad S e := by
  obtain ⟨h1, h2⟩ := mem_unipRad.1 hg
  refine mem_unipRad.2 ⟨mem_parab.2 fun i j hij => ?_, fun a i j => ?_⟩
  · show f ((g : Matrix n n R) i j) = 0
    rw [mem_parab.1 h1 i j hij, map_zero]
  · show f ((g : Matrix n n R) _ _) = _
    rw [h2 a i j, one_apply, one_apply]
    split_ifs <;> simp

end Rad

theorem isCuspidal_comp_generalLinearGroupMap {k k' : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] [Field k'] [ValuativeRel k'] [TopologicalSpace k']
    [IsNonarchimedeanLocalField k'] (i : k ≃+* k') (hi : Continuous i.symm) {n : Type} [Fintype n]
    [DecidableEq n] {V : Type} [AddCommGroup V] [Module ℂ V] (π : Representation ℂ (GL n k) V)
    (h : IsCuspidal π) : IsCuspidal (π.comp (GeneralLinearGroup.map (n := n) i.symm.toRingHom)) := by
  set M := GeneralLinearGroup.map (n := n) i.symm.toRingHom with hM
  have hc : Continuous M :=
    Units.continuous_iff.2 ⟨continuous_matrix fun a b => hi.comp (Units.continuous_val.matrix_elem a b),
      continuous_matrix fun a b => hi.comp (Units.continuous_coe_inv.matrix_elem a b)⟩
  refine ⟨fun v => (h.1 v).preimage hc, fun s d e he => ?_⟩
  have hmem : ∀ u ∈ unipRad k' e, M u ∈ unipRad k e := fun u hu => map_mem_unipRad_of_ringHom _ hu
  have hsurj : ∀ w ∈ unipRad k e, ∃ u ∈ unipRad k' e, M u = w := fun w hw =>
    ⟨GeneralLinearGroup.map i.toRingHom w, map_mem_unipRad_of_ringHom _ hw,
      Units.ext (Matrix.ext fun _ _ => i.symm_apply_apply _)⟩
  have hinj : Function.Injective M := fun x y hxy => Units.ext (Matrix.ext fun a b =>
    i.symm.injective (congrArg (fun g : GL n k => (g : Matrix n n k) a b) hxy))
  have hne : unipRad k e ≠ ⊥ := fun hb => he ((Subgroup.eq_bot_iff_forall _).2 fun u hu =>
    hinj ((((Subgroup.eq_bot_iff_forall _).1 hb) _ (hmem u hu)).trans (map_one M).symm))
  have h1 : twKer (π.comp M) (unipRad k' e) 1 = twKer π (unipRad k e) 1 := by
    unfold twKer
    congr 1
    ext w
    constructor
    · rintro ⟨u, v, rfl⟩
      exact ⟨⟨M u, hmem u u.2⟩, v, by simp⟩
    · rintro ⟨u, v, rfl⟩
      obtain ⟨u', hu', hu⟩ := hsurj u u.2
      exact ⟨⟨u', hu'⟩, v, by simp [hu]⟩
  exact Submodule.Quotient.subsingleton_iff.2 (h1 ▸ Submodule.Quotient.subsingleton_iff.1 (h.2 s d e hne))

end GlobalTheory.LocGL
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LNotMemGset
section
open NumberField IsDedekindDomain Formalism Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Module

namespace GlobalTheory.AtQDTypes

theorem g_ne_q_d (D : D7) (k : Fin 2) : D.host.g k ≠ D.host.q ∧ D.host.g k ≠ D.host.d := by
  have hc := D.ntypes.g_cond k
  have hq8 := D.host.hyp.2.2.1
  have hd16 := D.host.hyp.2.2.2.1
  constructor
  · intro h
    have h1 : D.host.g k % D.host.q = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.q ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.d, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega
  · intro h
    have h1 : D.host.g k % D.host.d = 1 := by
      rw [← Nat.mod_mod_of_dvd _ (show D.host.d ∣ D.host.QS * D.host.q * D.host.d from
        ⟨D.host.QS * D.host.q, by ring⟩), hc]
      exact Nat.mod_eq_of_lt (by omega)
    rw [h, Nat.mod_self] at h1
    omega

theorem l_not_mem_gset {D : D7} (i : D.nd.Loc) (h : D.nd.l i = D.host.q ∨ D.nd.l i = D.host.d) :
    D.nd.l i ∉ TwistedPlaces.gset D := by
  unfold TwistedPlaces.gset
  intro hm
  rw [Finset.mem_insert, Finset.mem_singleton] at hm
  rcases hm with hm | hm <;> rcases h with h | h
  · exact (g_ne_q_d D 0).1 (hm ▸ h)
  · exact (g_ne_q_d D 0).2 (hm ▸ h)
  · exact (g_ne_q_d D 1).1 (hm ▸ h)
  · exact (g_ne_q_d D 1).2 (hm ▸ h)

end GlobalTheory.AtQDTypes

theorem GlobalTheory.restPt_atQD : GlobalTheory.Published.FontaineBcris → ∀ (D : D7) (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))), GlobalTheory.PtCore.PtFam D r ρ → SumRepresentations.Conclusion41 D → GlobalTheory.SplitCoef.OSplit D → ∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → ∀ π ∈ D.nd.Zgood i, RestPt i (r i) (ρ i) π :=
  fun hF D r ρ hP h41 hO i hi π hπ =>
    GlobalTheory.T.restriction_at_good_points hF D r ρ hP h41 hO i (GlobalTheory.AtQDTypes.l_not_mem_gset i hi.1.1) π hπ
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LagFrameIsLagFrame
section
noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.RawLift

variable {D : D7}

def lagFrame (W : HSp D) (Y : Lag W) :
    Matrix (Fin W.rank) (Fin W.rank) D.host.E × Matrix (Fin W.rank) (Fin W.rank) D.host.E :=
  let b := Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1
  (Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a,
    Matrix.of fun a j => (b j : (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a)

theorem lagFrame_isLagFrame (W : HSp D) (Y : Lag W) : IsLagFrame W Y (lagFrame W Y) := by
  unfold IsLagFrame lagFrame
  have h : (Set.range fun j =>
      ((fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).1 a) a j),
        (fun a => (Matrix.of fun a j => ((Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) j :
          (Fin W.rank → D.host.E) × (Fin W.rank → D.host.E)).2 a) a j))) =
      (Y.1.subtype) '' Set.range (Module.finBasisOfFinrankEq D.host.E Y.1 Y.2.1) := by
    rw [← Set.range_comp]
    rfl
  rw [h, Submodule.span_image, Module.Basis.span_eq, Submodule.map_top, Submodule.range_subtype]

end GlobalTheory.RawLift

end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LintegralThetaSeriesUnfoldMirabolicStatement
section
open NumberField MeasureTheory Matrix GlobalTheory.CuspRep GlobalTheory.MirTower
open scoped ENNReal
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.lintegral_theta_series_unfold_mirabolic : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (ha : 0 < a) (μ : Measure (GA E a)) [μ.IsHaarMeasure] (𝓕 𝓕P : Set (GA E a)), IsFundamentalDomain (ratGL E a).range 𝓕 μ → IsFundamentalDomain (ratMirU E a (a - 1)) 𝓕P μ → ∀ F : GA E a → (Fin a → Ad E) → ℝ≥0∞, (∀ v : Fin a → E, Measurable fun g : GA E a => F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (v i)) g.val)) → (∀ (γ : GL (Fin a) E) g y, F (ratGL E a γ * g) y = F g y) → ∫⁻ g in 𝓕, ∑' ξ : {v : Fin a → E // v ≠ 0}, F g (Matrix.vecMul (fun i => algebraMap E (Ad E) (ξ.1 i)) g.val) ∂μ = ∫⁻ g in 𝓕P, F g (g.val ⟨a - 1, Nat.sub_lt ha Nat.one_pos⟩) ∂μ := by
  first | exact @GlobalTheory.ThetaUnfold.lintegral_theta_unfold | exact GlobalTheory.ThetaUnfold.lintegral_theta_unfold | (intros; apply GlobalTheory.ThetaUnfold.lintegral_theta_unfold <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalComparisonHoldsStatement
section
open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc TensorProduct GlobalTheory.NL Formalism.MainNotions.DeltaInvariantLattices
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.local_comparison_of_cmpOf : ∀ (D : Formalism.BasicNotions.D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), p5eL D.loc D.locA HW F := by
  first | exact @GlobalTheory.NL.SandJumps.main | exact GlobalTheory.NL.SandJumps.main | (intros; apply GlobalTheory.NL.SandJumps.main <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMtMulLeftAdelicMatrixHaarEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mt_mul_left_adelicMatrix_haar_eq : ∀ (D : D7) (V : HSp D) (m : ℕ) (g : GA D V) (μ : Measure (Mx D V.rank m)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D V.rank m => (HMul.hMul (mt V g) (x : Matrix (Fin V.rank) (Fin m) (AE D)) : Mx D V.rank m)) = μ := by
  first | exact @GlobalTheory.map_mt_mul_eq | exact GlobalTheory.map_mt_mul_eq | (intros; apply GlobalTheory.map_mt_mul_eq <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MapMulRightUnitaryGramAdelicMatrixHaarEqStatement
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.map_mul_right_unitaryGram_adelicMatrix_haar_eq : ∀ (D : D7) (N m : ℕ) (K : Matrix (Fin N) (Fin N) D.host.E), (∀ a b, D.sp.cm.sig (K b a) = K a b) → K.det ≠ 0 → ∀ (g : HA (AF D.host.F) D.sp.cm.sig K) (μ : Measure (Mx D m N)), μ.IsAddHaarMeasure → μ.map (fun x : Mx D m N => (HMul.hMul (x : Matrix (Fin m) (Fin N) (AE D)) ((HA.mat (AF D.host.F) D.sp.cm.sig K g).1 : Matrix (Fin N) (Fin N) (AE D)) : Mx D m N)) = μ := by
  first | exact @GlobalTheory.mul_unitary_map_haar | exact GlobalTheory.mul_unitary_map_haar | (intros; apply GlobalTheory.mul_unitary_map_haar <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemNatMultipleIntegralFiniteAdelesIffIdealFiniteStatement
section
open NumberField IsDedekindDomain
open scoped nonZeroDivisors
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.mem_natMultipleIntegralFiniteAdeles_iff_idealFiniteAdeles : ∀ (E : Type) [Field E] [NumberField E] (N : ℕ), 0 < N → ∀ (J : (FractionalIdeal (𝓞 E)⁰ E)ˣ), (J : FractionalIdeal (𝓞 E)⁰ E) = FractionalIdeal.spanSingleton (𝓞 E)⁰ (N : E) → ∀ z : FiniteAdeleRing (𝓞 E) E, z ∈ GlobalTheory.RSJ.natLat E N ↔ z ∈ GroundTheory.Global.idealFiniteAdeles J := by
  first | (exact @GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (exact GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles) | (intros; apply GlobalTheory.RSJ.natLat_iff_mem_idealFiniteAdeles  <;> assumption)
end

