import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsNotRelZero
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.UnitaryConjugation
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1674
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1702
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1728
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0063
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0015
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0515
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1706
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1726
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1723
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsTypeIsRealConst
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0028
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.Bundle0100
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Bundle0015
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.Bundle0025
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0008
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.Bundle0014
import Formalism.LocalToGlobal.KernelLattices.TopPin
import Formalism.LocalToGlobal.KernelLattices.Bundle0001

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HermitianTensorSkewHermitianLatticeOpenCompact
section
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.IndefR.Links
open IsDedekindDomain NumberField MeasureTheory Matrix
open Classical
open scoped TensorProduct ComplexConjugate GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open GlobalTheory.FunObj GlobalTheory.ChiGrid GlobalTheory.SplitFlip GlobalTheory.SplitWeil GlobalTheory.StdFrames Formalism.L2.DIV
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryConjugation (spV spW spW₁ spV₁ alpha beta Num skewGram blk conjU)
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model HasExp SplitsFully Chars)

attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw

noncomputable section

namespace GlobalTheory.LatOpenCpt

open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem exists_zsmul_mem {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) (z : Fin n → E) : ∃ m : ℤ, m ≠ 0 ∧ m • z ∈ L := by
  first
  | exact @_root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem
  | exact _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem
  | (apply _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> assumption)
  | (intros; apply _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> assumption)
  | (intros; apply @_root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.IntegerMultipleMembership.exists_int_smul_mem ..)

theorem vecMulVec_mem {E : Type} [Field E] [NumberField E] {n d : ℕ} {LX : Submodule (𝓞 E) (Fin n → E)}
    {LY : Submodule (𝓞 E) (Fin d → E)} (sX : Finset LX) (hsX : Submodule.span ℤ (sX : Set LX) = ⊤) (sY : Finset LY)
    (hsY : Submodule.span ℤ (sY : Set LY) = ⊤) (H : AddSubgroup (Matrix (Fin n) (Fin d) E))
    (hH : ∀ x ∈ sX, ∀ y ∈ sY, vecMulVec (x : Fin n → E) (y : Fin d → E) ∈ H) :
    ∀ x ∈ LX, ∀ y ∈ LY, vecMulVec x y ∈ H := by
  intro x hx y hy
  suffices h : ∀ z : LX, ∀ w : LY, vecMulVec (z : Fin n → E) (w : Fin d → E) ∈ H from h ⟨x, hx⟩ ⟨y, hy⟩
  intro z w
  have hz : z ∈ Submodule.span ℤ (sX : Set LX) := by rw [hsX]; trivial
  have hw : w ∈ Submodule.span ℤ (sY : Set LY) := by rw [hsY]; trivial
  induction hz using Submodule.span_induction with
  | mem a ha =>
    induction hw using Submodule.span_induction with
    | mem b hb => exact hH a ha b hb
    | zero =>
      have : vecMulVec (a : Fin n → E) ((0 : LY) : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
      rw [this]; exact H.zero_mem
    | add b c _ _ hb hc => rw [Submodule.coe_add, vecMulVec_add]; exact H.add_mem hb hc
    | smul k b _ hb => rw [Submodule.coe_smul_of_tower, vecMulVec_smul]; exact H.zsmul_mem hb k
  | zero =>
    have : vecMulVec ((0 : LX) : Fin n → E) (w : Fin d → E) = 0 := by ext; simp [vecMulVec_apply]
    rw [this]; exact H.zero_mem
  | add a b _ _ ha hb => rw [Submodule.coe_add, add_vecMulVec]; exact H.add_mem ha hb
  | smul k a _ ha => rw [Submodule.coe_smul_of_tower, smul_vecMulVec]; exact H.zsmul_mem ha k

theorem exists_gen {E : Type} [Field E] [NumberField E] {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : L.IsLattice E) : ∃ s : Finset L, Submodule.span ℤ (s : Set L) = ⊤ := by
  haveI : Module.Finite (𝓞 E) L := Module.Finite.iff_fg.mpr hL.fg
  haveI : Module.Finite ℤ L := Module.Finite.trans (𝓞 E) L
  exact Module.Finite.fg_top

theorem locCo_smul {F : Type} [Field F] [NumberField F] {W : Type} [AddCommGroup W] [Module (AF F) W]
    {B : W → W → AF F} {κ : Type} [Fintype κ] (co : GlobalTheory.WeilM.Darboux B κ) (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (a : AF F) (w : W) :
    GlobalTheory.LatVac.locCo co v (a • w) = GlobalTheory.AdelicU.evFin F v a • GlobalTheory.LatVac.locCo co v w := by
  simp only [GlobalTheory.LatVac.locCo, AddMonoidHom.coe_mk, ZeroHom.coe_mk, map_smul]
  ext k <;> simp [smul_eq_mul, map_mul]

end GlobalTheory.LatOpenCpt

namespace GlobalTheory.LatOpenCpt
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels

theorem incM_single {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    (i : Fin n) (j : Fin d) (e : E) :
    incM F (Matrix.single i j e) = Matrix.single i j ((1 : AF F) ⊗ₜ[F] e) := by
  ext a b
  simp only [incM, Matrix.map_apply, Matrix.single_apply]
  split_ifs <;> first | rfl | exact map_zero _

theorem single_eq_vecMulVec {E : Type} [Field E] {n d : ℕ} (i : Fin n) (j : Fin d) (e : E) :
    Matrix.single i j e = vecMulVec (Pi.single i e) (Pi.single j 1) := by
  ext a b
  simp only [Matrix.single_apply, vecMulVec_apply, Pi.single_apply]
  split_ifs <;> simp_all

theorem span_top {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n d : ℕ}
    {LX : Submodule (𝓞 E) (Fin n → E)} {LY : Submodule (𝓞 E) (Fin d → E)} (hX : LX.IsLattice E) (hY : LY.IsLattice E)
    {ι : Type} (t : ι → Matrix (Fin n) (Fin d) E)
    (ht : ∀ x ∈ LX, ∀ y ∈ LY, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)))
    (Z : Matrix (Fin n) (Fin d) (AE F E)) : Z ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) := by
  set S := Submodule.span (AF F) (Set.range fun i => incM F (t i))
  have hzs : ∀ (k : ℤ) (P : Matrix (Fin n) (Fin d) E), incM F (k • P) = k • incM F P := fun k P => by
    ext a b; simp [incM, map_zsmul]
  have hall : ∀ (x : Fin n → E) (y : Fin d → E), incM F (vecMulVec x y) ∈ S := by
    intro x y
    obtain ⟨m, hm, hmx⟩ := exists_zsmul_mem LX hX x
    obtain ⟨m', hm', hmy⟩ := exists_zsmul_mem LY hY y
    have h1 := ht _ hmx _ hmy
    rw [smul_vecMulVec, vecMulVec_smul, smul_smul, hzs] at h1
    have hk : ((m * m' : ℤ) : F) ≠ 0 := Int.cast_ne_zero.mpr (mul_ne_zero hm hm')
    have := S.smul_mem (algebraMap F (AF F) ((m * m' : ℤ) : F)⁻¹) h1
    rwa [← Int.cast_smul_eq_zsmul (AF F), smul_smul, ← map_intCast (algebraMap F (AF F)), ← map_mul,
      inv_mul_cancel₀ hk, map_one, one_smul] at this
  have hsingle : ∀ (i : Fin n) (j : Fin d) (z : AE F E), Matrix.single i j z ∈ S := by
    intro i j z
    induction z using TensorProduct.induction_on with
    | zero => rw [Matrix.single_zero]; exact S.zero_mem
    | tmul a e =>
      have h := S.smul_mem a (hall (Pi.single i e) (Pi.single j 1))
      rw [← single_eq_vecMulVec, incM_single, Matrix.smul_single, TensorProduct.smul_tmul', smul_eq_mul, mul_one] at h
      exact h
    | add z z' hz hz' => rw [Matrix.single_add]; exact S.add_mem hz hz'
  rw [Matrix.matrix_eq_sum_single Z]
  exact S.sum_mem fun i _ => S.sum_mem fun j _ => hsingle i j (Z i j)

theorem main : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) {n d : ℕ} (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E n)
    (Y : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Spc F E d) (r s r' s' : ℕ),
    X.IsHerm σ B r s → Y.IsSkew σ B r' s' → ∀ M : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Model σ X Y,
    (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        M.co.e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.incM F x) = (fun k => algebraMap F (AF F) (y k), fun k => algebraMap F (AF F) (z k))) →
    ∀ v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F,
      IsOpen (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) ∧
      IsCompact (((GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) :
        AddSubgroup ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) : Set ((Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v))) := by
  intro F E _ _ _ _ _ σ B n d X Y r s r' s' hX hY M _ v
  obtain ⟨sX, hsX⟩ := exists_gen X.L hX.lat
  obtain ⟨sY, hsY⟩ := exists_gen Y.L hY.lat
  let ι := ↥sX × ↥sY
  let t : ι → Matrix (Fin n) (Fin d) E := fun i => vecMulVec ((i.1 : X.L) : Fin n → E) ((i.2 : Y.L) : Fin d → E)
  let ρ : ι → (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) := fun i => GlobalTheory.LatVac.locCo M.co v (incM F (t i))
  let φ : (ι → Fv F v) →ₗ[Fv F v] (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
    { toFun := fun f => ∑ i, f i • ρ i
      map_add' := fun f g => by simp [add_smul, Finset.sum_add_distrib]
      map_smul' := fun c f => by simp [Finset.smul_sum, smul_smul] }
  have hφ : ∀ f, φ f = ∑ i, f i • ρ i := fun f => rfl
  let Opi : AddSubgroup (ι → Fv F v) := AddSubgroup.pi Set.univ fun _ => (v.adicCompletionIntegers F).toSubring.toAddSubgroup
  have hO : ∀ f, f ∈ Opi ↔ ∀ i, f i ∈ v.adicCompletionIntegers F := fun f => by
    simp only [Opi, AddSubgroup.mem_pi, Set.mem_univ, true_implies]; rfl
  set Λ := (latAtV X Y v).map (GlobalTheory.LatVac.locCo M.co v) with hΛdef
  have hgen : ∀ x ∈ X.L, ∀ y ∈ Y.L, ∀ a : Fv F v, a ∈ v.adicCompletionIntegers F →
      a • GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Λ := by
    intro x hx y hy a ha
    refine ⟨GlobalTheory.LatVac.liftV v a • incM F (vecMulVec x y), AddSubgroup.subset_closure
      ⟨GlobalTheory.LatVac.liftV v a, GlobalTheory.LatVac.at_liftV v a, by rw [GlobalTheory.LatVac.evFin_liftV]; exact ha, x, hx, y, hy, rfl⟩, ?_⟩
    rw [locCo_smul, GlobalTheory.LatVac.evFin_liftV]
  have hle1 : Opi.map φ.toAddMonoidHom ≤ Λ := by
    rintro _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    show ∑ i, f i • ρ i ∈ Λ
    exact Λ.sum_mem fun i _ => hgen _ (i.1 : X.L).2 _ (i.2 : Y.L).2 _ (hf i)
  have hsmul : ∀ a ∈ v.adicCompletionIntegers F, ∀ w ∈ Opi.map φ.toAddMonoidHom, a • w ∈ Opi.map φ.toAddMonoidHom := by
    rintro a ha _ ⟨f, hf, rfl⟩
    replace hf := (hO _).1 hf
    exact ⟨a • f, (hO _).2 fun i => mul_mem ha (hf i), (φ.map_smul a f)⟩
  have hρ : ∀ x ∈ X.L, ∀ y ∈ Y.L,
      GlobalTheory.LatVac.locCo M.co v (incM F (vecMulVec x y)) ∈ Opi.map φ.toAddMonoidHom := by
    let rA : Matrix (Fin n) (Fin d) E →+ (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) :=
      (GlobalTheory.LatVac.locCo M.co v).comp (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)
    refine vecMulVec_mem sX hsX sY hsY ((Opi.map φ.toAddMonoidHom).comap rA) ?_
    intro x hx y hy
    refine ⟨Pi.single (⟨x, hx⟩, ⟨y, hy⟩) 1, (hO _).2 fun i => ?_, ?_⟩
    · by_cases h : i = (⟨x, hx⟩, ⟨y, hy⟩)
      · rw [h]; simp
      · simp [Pi.single_apply, h]
    · show ∑ i, (Pi.single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (1 : Fv F v) : ι → Fv F v) i • ρ i = _
      rw [Finset.sum_eq_single ((⟨x, hx⟩, ⟨y, hy⟩) : ι) (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simp only [Pi.single_eq_same, one_smul]
      rfl
  have hle2 : Λ ≤ Opi.map φ.toAddMonoidHom := by
    rw [hΛdef, AddSubgroup.map_le_iff_le_comap, latAtV, AddSubgroup.closure_le]
    rintro _ ⟨a, -, ha, x, hx, y, hy, rfl⟩
    rw [SetLike.mem_coe, AddSubgroup.mem_comap, locCo_smul]
    exact hsmul _ ha _ (hρ x hx y hy)
  have hΛ : Λ = Opi.map φ.toAddMonoidHom := le_antisymm hle2 hle1
  have hsurj : ∀ u, ∃ f, φ f = u := by
    intro u
    let U : (Fin n × Fin d → AF F) × (Fin n × Fin d → AF F) :=
      (fun k => GlobalTheory.LatVac.liftV v (u.1 k), fun k => GlobalTheory.LatVac.liftV v (u.2 k))
    have ht : ∀ x ∈ X.L, ∀ y ∈ Y.L, incM F (vecMulVec x y) ∈ Submodule.span (AF F) (Set.range fun i => incM F (t i)) :=
      vecMulVec_mem sX hsX sY hsY ((Submodule.span (AF F) (Set.range fun i => incM F (t i))).toAddSubgroup.comap
        (AddMonoidHom.mapMatrix (inclR (F := F) (AF F)).toAddMonoidHom)) (fun x hx y hy => Submodule.subset_span ⟨(⟨x, hx⟩, ⟨y, hy⟩), rfl⟩)
    have hZ := span_top hX.lat hY.lat t ht (M.co.e.symm U)
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun _).1 hZ
    refine ⟨fun i => GlobalTheory.AdelicU.evFin F v (c i), ?_⟩
    rw [hφ]
    have hu : GlobalTheory.LatVac.locCo M.co v (M.co.e.symm U) = u := by
      ext k <;> simp [GlobalTheory.LatVac.locCo, U, GlobalTheory.LatVac.evFin_liftV]
    rw [← hu, ← hc, map_sum]
    exact Finset.sum_congr rfl fun i _ => (locCo_smul _ _ _ _).symm
  have hOc : IsCompact (v.adicCompletionIntegers F : Set (Fv F v)) := PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v
  have hOo : IsOpen (v.adicCompletionIntegers F : Set (Fv F v)) := Valued.isOpen_valuationSubring _
  have hφc : Continuous φ := by
    rw [show (φ : (ι → Fv F v) → _) = fun f => ∑ i, f i • ρ i from rfl]
    exact continuous_finset_sum _ fun i _ => (continuous_apply i).smul continuous_const
  have hset : ((Opi.map φ.toAddMonoidHom : AddSubgroup _) : Set _) =
      φ '' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
    ext w
    simp only [AddSubgroup.coe_map, Set.mem_image, SetLike.mem_coe, hO, Set.mem_pi, Set.mem_univ, true_implies]
    rfl
  choose f1 hf1 using fun k : Fin n × Fin d => hsurj (Pi.single k 1, 0)
  choose f2 hf2 using fun k : Fin n × Fin d => hsurj (0, Pi.single k 1)
  let sec : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v) → ι → Fv F v :=
    fun u => ∑ k, u.1 k • f1 k + ∑ k, u.2 k • f2 k
  have hsec : ∀ u, φ (sec u) = u := by
    intro u
    simp only [sec, map_add, map_sum, map_smul, hf1, hf2]
    ext k <;> simp [Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Pi.single_apply]
  have hsc : Continuous sec :=
    (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_fst).smul continuous_const).add
      (continuous_finset_sum _ fun k _ => ((continuous_apply k).comp continuous_snd).smul continuous_const)
  constructor
  · apply AddSubgroup.isOpen_of_mem_nhds (g := 0)
    have hU : IsOpen (sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v))) :=
      (isOpen_set_pi Set.finite_univ fun _ _ => hOo).preimage hsc
    have h0 : (0 : (Fin n × Fin d → Fv F v) × (Fin n × Fin d → Fv F v)) ∈
        sec ⁻¹' Set.pi Set.univ fun _ => (v.adicCompletionIntegers F : Set (Fv F v)) := by
      intro i _; simp [sec]
    refine Filter.mem_of_superset (hU.mem_nhds h0) ?_
    intro u hu
    rw [SetLike.mem_coe, hΛ]
    exact ⟨sec u, (hO _).2 fun i => hu i (Set.mem_univ _), hsec u⟩
  · rw [hΛ, hset]
    exact (isCompact_univ_pi fun _ => hOc).image hφc

end GlobalTheory.LatOpenCpt
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateLatticeEqRowSpaceOfSandwichDatum
section
set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat.RowSpace

section SlopeTestRemainingChoices

variable {p : ℕ} [Fact p.Prime] {O : Type} [CommRing O] [Fact ¬IsUnit (p : O)]
  [IsAdicComplete (Ideal.span {(p : O)}) O]

variable (p O) in

def ghostHom (n : ℕ) : Ainf p O →+* O where
  toFun := ghost p O n
  map_one' := by
    show WittVector.fontaineTheta O p (_ ^[n] 1) = 1
    rw [iterate_map_one, map_one]
  map_mul' := ghost_mul n
  map_zero' := ghost_zero n
  map_add' := ghost_add n

theorem ghostHom_apply (n : ℕ) (a : Ainf p O) : ghostHom p O n a = ghost p O n a := rfl

def dotLin {R : Type} [CommRing R] {h : ℕ} (v : Fin h → R) : (Fin h → R) →ₗ[R] R where
  toFun w := v ⬝ᵥ w
  map_add' := dotProduct_add v
  map_smul' c w := by simp [dotProduct_smul]

theorem dotLin_apply {R : Type} [CommRing R] {h : ℕ} (v w : Fin h → R) : dotLin v w = v ⬝ᵥ w := rfl

def toA {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (t : G.Tate) :
    Fin h → Ainf p O := fun i => ofPadic p O (e t i)

theorem toA_add {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (t t' : G.Tate) : toA e (t + t') = toA e t + toA e t' := by
  ext i; simp [toA]

theorem toA_smul {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (c : ℤ_[p]) (t : G.Tate) : toA e (c • t) = ofPadic p O c • toA e t := by
  ext i; simp [toA]

theorem toA_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toA e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toA, Pi.single_apply, hij]

theorem toO_single {G : PDivGroup p O} {h : ℕ} (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p]))
    (i : Fin h) : toO e (e.symm (Pi.single i 1)) = Pi.single i 1 := by
  ext j; by_cases hij : j = i <;> simp [toO, Pi.single_apply, hij]

def rowMap {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) : (Fin h → Ainf p O) →ₗ[Ainf p O] TDual G where
  toFun r :=
    { toFun := fun t => r ⬝ᵥ (F *ᵥ toA e t)
      map_add' := fun t t' => by rw [toA_add, mulVec_add, dotProduct_add]
      map_smul' := fun c t => by
        rw [toA_smul, mulVec_smul, dotProduct_smul] }
  map_add' r r' := LinearMap.ext fun t => add_dotProduct r r' _
  map_smul' a r := LinearMap.ext fun t => smul_dotProduct a r _

theorem rowMap_apply {G : PDivGroup p O} {h : ℕ} (F : Matrix (Fin h) (Fin h) (Ainf p O))
    (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (r : Fin h → Ainf p O) (t : G.Tate) :
    rowMap F e r t = r ⬝ᵥ (F *ᵥ toA e t) := rfl

theorem F_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ X : Matrix (Fin h) (Fin h) O,
      D.F.map (ghostHom p O n) = X * D.F.map (WittVector.fontaineTheta O p) := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.one_mul]; rfl⟩
  | succ n ih =>
    obtain ⟨X, hX⟩ := ih
    refine ⟨D.Ψ.map (ghostHom p O (n + 1)) * X, ?_⟩
    have e1 : D.F.map (ghostHom p O (n + 1)) =
        D.Ψ.map (ghostHom p O (n + 1)) * D.F.map (ghostHom p O n) := by
      conv_lhs => rw [D.F_eq]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hX, Matrix.mul_assoc]

theorem G_map_ghost {ε : PreTilt O p} {h : ℕ} (D : Datum ε h ℤ_[p])
    (hG : D.G = D.G.map (phiInv p O) * D.Ψ')
    (hphi : ∀ n a, ghost p O (n + 1) (phiInv p O a) = ghost p O n a) (n : ℕ) :
    ∃ Y : Matrix (Fin h) (Fin h) O,
      D.G.map (ghostHom p O n) = D.G.map (WittVector.fontaineTheta O p) * Y := by
  induction n with
  | zero => exact ⟨1, by rw [Matrix.mul_one]; rfl⟩
  | succ n ih =>
    obtain ⟨Y, hY⟩ := ih
    refine ⟨Y * D.Ψ'.map (ghostHom p O (n + 1)), ?_⟩
    have e1 : D.G.map (ghostHom p O (n + 1)) =
        D.G.map (ghostHom p O n) * D.Ψ'.map (ghostHom p O (n + 1)) := by
      conv_lhs => rw [hG]
      rw [Matrix.map_mul, Matrix.map_map]
      congr 1
      ext i j
      exact hphi n _
    rw [e1, hY, Matrix.mul_assoc]

end SlopeTestRemainingChoices

theorem latt_eq_rowSpace : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)] [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O → ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε), ∀ (G : PDivGroup p O) (h : ℕ) (D : Datum ε h ℤ_[p]) (e : G.Tate ≃ₗ[ℤ_[p]] (Fin h → ℤ_[p])) (fil : G.dual.omega ≃ₗ[O] D.Fil), (∀ t, D.al (toO e t) = (fil (hodgeTate G t) : Fin h → O)) → ∃ L : (Fin h → Ainf p O) ≃ₗ[Ainf p O] latt G, ∀ r t, (L r).1 t = r ⬝ᵥ (D.F *ᵥ fun i => ofPadic p O (e t i)) := by
  intro p _ C _ _ _ v O _ _ _ _ _ hv ε hε G h D e fil hal
  obtain ⟨-, hofP, hmu, -, -, hphi⟩ := GlobalTheory.T.ainfGhostThetaFrobIter_values_xi_mu_padic p C v O hv ε hε
  have hε1 : IsPrimitiveRoot (root ε).untilt p := by simpa [zeta] using hε 1
  obtain ⟨hdom, -, -, -, hν, hξ, -⟩ := GlobalTheory.AinfXi.ainf_local_xi_order p C v O hv ε hε1
  haveI := hdom
  have hμ : Sandwich.mu ε ≠ 0 := by
    rw [← xi_mul_nu]
    exact mul_ne_zero hξ fun h0 => hν (by rw [h0, map_zero])
  have hFG : D.F * D.G = Sandwich.mu ε • (1 : Matrix (Fin h) (Fin h) (Ainf p O)) :=
    GlobalTheory.SelfDualFil.mul_eq_smul_comm hμ D.G_mul_F
  have hGeq := GlobalTheory.SelfDualFil.G_eq hμ hξ D
  have hθμ : WittVector.fontaineTheta O p (Sandwich.mu ε) = 0 := hmu 0

  have hzero : ∀ X Y : Matrix (Fin h) (Fin h) (Ainf p O), X * Y = Sandwich.mu ε • 1 →
      ∀ w : Fin h → O, X.map (WittVector.fontaineTheta O p) *ᵥ
        (Y.map (WittVector.fontaineTheta O p) *ᵥ w) = 0 := by
    intro X Y hXY w
    rw [mulVec_mulVec, ← Matrix.map_mul, hXY]
    ext i
    simp [Matrix.mulVec, dotProduct, hθμ]
  have halFil : ∀ w, D.al w ∈ D.Fil := fun w => by
    rw [Datum.Fil, LinearMap.mem_ker, Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ D.G_mul_F w
  have halbb : ∀ u, D.al (D.bb u) = 0 := fun u => by
    rw [Datum.bb, Datum.al, toLin'_apply, toLin'_apply]
    exact hzero _ _ hFG u

  have hghostA : ∀ n t, (ghostHom p O n) ∘ toA e t = toO e t := fun n t =>
    funext fun i => hofP n _
  have hmem : ∀ r, rowMap D.F e r ∈ latt G := by
    intro r n
    obtain ⟨X, hX⟩ := F_map_ghost D hphi n
    refine ⟨dotLin ((ghostHom p O n ∘ r) ᵥ* X) ∘ₗ (D.Fil.subtype ∘ₗ fil.toLinearMap),
      fun t => ?_⟩
    rw [rowMap_apply, ← ghostHom_apply, RingHom.map_dotProduct]
    have e1 : (ghostHom p O n) ∘ (D.F *ᵥ toA e t) = X *ᵥ D.al (toO e t) := by
      funext i
      rw [Function.comp_apply, RingHom.map_mulVec, hghostA, hX, ← mulVec_mulVec, Datum.al,
        toLin'_apply]
    rw [e1, hal, dotProduct_mulVec]
    rfl
  let Φ := (rowMap D.F e).codRestrict (latt G) hmem
  have hinj : Function.Injective Φ := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro r hr
    have h1 : ∀ t, r ⬝ᵥ (D.F *ᵥ toA e t) = 0 := fun t =>
      congrArg (fun y : latt G => y.1 t) hr
    have h2 : r ᵥ* D.F = 0 := by
      funext i
      have := h1 (e.symm (Pi.single i 1))
      rw [toA_single, dotProduct_mulVec] at this
      simpa using this
    have h3 : Sandwich.mu ε • r = 0 := by
      have := congrArg (fun z => z ᵥ* D.G) h2
      simp only [vecMul_vecMul, hFG, vecMul_smul, vecMul_one, zero_vecMul] at this
      exact this
    exact (smul_eq_zero.1 h3).resolve_left hμ
  have hsurj : Function.Surjective Φ := by
    intro y
    set s : Fin h → Ainf p O := fun i => y.1 (e.symm (Pi.single i 1)) with hs
    have hy : ∀ t, y.1 t = s ⬝ᵥ toA e t := by
      intro t
      have ht : t = ∑ i, e t i • e.symm (Pi.single i 1) := by
        apply e.injective
        rw [map_sum]
        ext j
        simp [Finset.sum_apply, Pi.single_apply]
      conv_lhs => rw [ht]
      rw [map_sum]
      simp only [LinearMap.map_smulₛₗ, dotProduct, toA, smul_eq_mul, s]
      exact Finset.sum_congr rfl fun i _ => mul_comm _ _
    have hdiv : ∀ j, Sandwich.mu ε ∣ (s ᵥ* D.G) j := by
      intro j
      refine GlobalTheory.T.ainfTeichmullerMinusOne_dvd_of_ghost_components_zero p C v O hv ε hε _ fun n => ?_
      obtain ⟨x, hx⟩ := y.2 n
      set gs : Fin h → O := ghostHom p O n ∘ s with hgs
      have hgt : ∀ t, gs ⬝ᵥ toO e t = x (hodgeTate G t) := by
        intro t
        rw [← hx, hy, ← ghostHom_apply, RingHom.map_dotProduct, hghostA]
      have hl : dotLin gs = x ∘ₗ fil.symm.toLinearMap ∘ₗ D.al.codRestrict D.Fil halFil := by
        refine (Pi.basisFun O (Fin h)).ext fun i => ?_
        rw [Pi.basisFun_apply, ← toO_single e i, dotLin_apply, hgt]
        have e2 : D.al.codRestrict D.Fil halFil (toO e (e.symm (Pi.single i 1))) =
            fil (hodgeTate G (e.symm (Pi.single i 1))) := Subtype.ext (hal _)
        simp only [LinearMap.comp_apply, e2, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
      have hbb : gs ᵥ* D.G.map (WittVector.fontaineTheta O p) = 0 := by
        funext k
        have e3 := LinearMap.congr_fun hl (D.bb (Pi.single k 1))
        have e4 : D.al.codRestrict D.Fil halFil (D.bb (Pi.single k 1)) = 0 :=
          Subtype.ext (halbb _)
        rw [LinearMap.comp_apply, LinearMap.comp_apply, e4, map_zero, map_zero] at e3
        simp only [dotLin_apply, Datum.bb, toLin'_apply, dotProduct_mulVec] at e3
        simpa using e3
      obtain ⟨Y, hY⟩ := G_map_ghost D hGeq hphi n
      rw [← ghostHom_apply, RingHom.map_vecMul, hY, ← vecMul_vecMul, ← hgs, hbb, zero_vecMul]
      rfl
    choose r hr using hdiv
    have h1 : s ᵥ* D.G = Sandwich.mu ε • r := funext fun j => hr j
    have h2 : r ᵥ* D.F = s := by
      apply smul_right_injective (Fin h → Ainf p O) hμ
      change Sandwich.mu ε • (r ᵥ* D.F) = Sandwich.mu ε • s
      rw [← smul_vecMul, ← h1, vecMul_vecMul, D.G_mul_F, vecMul_smul, vecMul_one]
    refine ⟨r, Subtype.ext (LinearMap.ext fun t => ?_)⟩
    change r ⬝ᵥ (D.F *ᵥ toA e t) = y.1 t
    rw [hy, dotProduct_mulVec, h2]
  exact ⟨LinearEquiv.ofBijective Φ ⟨hinj, hsurj⟩, fun r t => rfl⟩

end GlobalTheory.PDivLat.RowSpace
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolAtlasIntegralFinSumCompactStatement
section
open Set Matrix MeasureTheory
open GlobalTheory.HermFrame
open scoped ComplexOrder
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.holAtlas_integral_fin_sum_compact : ∀ {M : Type} [TopologicalSpace M] [CompactSpace M] [T2Space M] [SecondCountableTopology M] [MeasurableSpace M] [BorelSpace M] {n : ℕ} (A : GlobalTheory.CxForm.HolAtlas M n) {N : ℕ} (α : Fin N → A.Fld), (∀ j, A.IsForm (α j)) → A.integral (∑ j, α j) = ∑ j, A.integral (α j) := by
  first | exact @GlobalTheory.CxForm.IntegralSum.integral_sum | exact GlobalTheory.CxForm.IntegralSum.integral_sum | (intros; apply GlobalTheory.CxForm.IntegralSum.integral_sum <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.HostCompatibilityStandardKernelDataTrueColumns
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.ColRows

theorem hostTie_stdKer : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → TC.Pins B X → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)), ∀ (L : SizeData₂ (I.rec7 l Z)) (hT : GatTies (I.rec7 l Z)) (Gi : G.Inst (I.rec7 l Z) L) (Gl : G.LatInst (I.rec7 l Z)) (K : G.Consts) (Y : DivX (I.rec7 l Z)) (cX : ExtraC) (ex : Extra (I.rec7 l Z) L hT Gi Gl K Y cX) (t : KerEntTied ex) (W : Formalism.L2.Col.Wts t.X t.Pr.Word (I.rec7 l Z).R) (Del h0 : ℕ), I.StdKer l Z t → GlobalTheory.IndefiniteRowSideFullHecke.PlaceLogThetaBounds.HostTie (ofRecord (I.rec7 l Z) L Del h0) t.seam t.Pr := by
  intro B X I hOk hPins l Z L hT Gi Gl K Y cX ex t W Del h0 hS
  obtain ⟨hX, hseam, hPr, -, -, -, -, -, -, -, -, -, -, -, -⟩ := hS
  cases t
  dsimp only at *
  subst hX
  obtain rfl := eq_of_heq hPr
  obtain rfl := eq_of_heq hseam
  exact GlobalTheory.CoreHt.host_tie_trueCols I hOk l Z L

end GlobalTheory.ColRows

end
end

