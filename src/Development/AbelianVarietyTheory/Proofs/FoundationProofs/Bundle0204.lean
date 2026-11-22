import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.BlochKatoPhases
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SelmerRankVanishing
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0235
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.Bundle0007
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0082
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0196
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0011
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0009
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0119
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0183
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0193
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0112
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0199
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0004
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0007
import CompanionTheory.EightfoldTheory.VariationTheory.AutomorphicForms.Newform
import Development.AbelianVarietyTheory.Definitions.Foundations.Bundle0001
import Development.AbelianVarietyTheory.Definitions.Foundations.PetEqRelIndexMulPetProd
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0048
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.Bundle0194

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LocalGaloisRepInvariantsFromFractionRing
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.BKDimNoInv

section Bridge

open Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (Bw : LocBridge l E Ω Gw O)

theorem rep_apply {m : ℕ} (r : ↥Gw →* GL (Fin m) O) (g : ↥(GK Bw.Kw)) (x : Fin m → ↥Bw.LL.1) :
    Bw.rep r g x = (((r (Bw.e.symm g) : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map Bw.toLL).mulVec x :=
  rfl

theorem toLL_injective : Function.Injective Bw.toLL :=
  Subtype.val_injective.comp Bw.eO.injective

theorem toLL_continuous : Continuous Bw.toLL :=
  continuous_subtype_val.comp Bw.eO_cont

theorem rep_continuous {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (x : Fin m → ↥Bw.LL.1) : Continuous fun g => Bw.rep r g x := by
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  simp only [rep_apply]
  exact ((hr.comp Bw.e_symm_cont).matrix_map (toLL_continuous Bw)).matrix_mulVec continuous_const

theorem localGaloisRep_invariants_from_fractionRing [IsDomain O] {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) : H0V (Bw.rep r) = ⊥ := by
  obtain ⟨_, -, hfr⟩ := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.1
  let φ : FractionRing O →+* ↥Bw.LL.1 := IsFractionRing.lift (g := Bw.toLL) (toLL_injective Bw)
  have hφ : ∀ a, φ (algebraMap O _ a) = Bw.toLL a := fun a => IsFractionRing.lift_algebraMap _ a
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨n, d, -, rfl⟩ := IsFractionRing.div_surjective (A := ↥(OL Bw.LL)) y
    refine ⟨algebraMap O _ (Bw.eO.symm n) / algebraMap O _ (Bw.eO.symm d), ?_⟩
    rw [map_div₀, hφ, hφ]
    simp [LocBridge.toLL]
  rw [eq_bot_iff]
  intro x hx
  choose x₀ hx₀ using fun a => hsurj (x a)
  have h0 : x₀ = 0 := by
    refine h x₀ fun g => ?_
    have h1 : Bw.rep r (Bw.e g) x = x := by
      have := (Submodule.mem_iInf _).1 hx (Bw.e g)
      rwa [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    rw [rep_apply, MulEquiv.symm_apply_apply] at h1
    funext a
    apply φ.injective
    rw [hx₀, ← congrFun h1 a]
    simp only [Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.map_apply, hφ, hx₀]
  rw [Submodule.mem_bot]
  funext a
  rw [← hx₀, h0]
  exact map_zero φ

noncomputable def grepOf {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O)) :
    GRep ↥(GK Bw.Kw) ℚ_[l] ↥Bw.LL.1 ↥(OL Bw.LL) :=
  haveI : IsTopologicalRing ↥Bw.LL.1 := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1.2.2.2.1
  { V := Fin m → ↥Bw.LL.1
    acg := inferInstance
    modLL := inferInstance
    modQp := inferInstance
    towQp := inferInstance
    modO := inferInstance
    towO := inferInstance
    fd := inferInstance
    top := inferInstance
    mtop := inferInstance
    cadd := inferInstance
    csmul := inferInstance
    ρ := Bw.rep r
    cont := rep_continuous Bw r hr }

set_option maxHeartbeats 1000000 in

theorem finrank_h1f_no_invariants [IsDomain O] (P : LocPrime l) {m : ℕ} (r : ↥Gw →* GL (Fin m) O)
    (hr : Continuous fun g => ((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O))
    (hBK : Formalism.MainNotions.LocalSituation.bkADim (P.PD Bw.Kw)) (hdR : Bw.IsdRW P r)
    (h : ∀ x : Fin m → FractionRing O, (∀ g : ↥Gw,
      (((r g : GL (Fin m) O) : Matrix (Fin m) (Fin m) O).map (algebraMap O (FractionRing O))).mulVec x = x) →
        x = 0) :
    (Module.finrank ↥Bw.LL.1 (FiniteCohomology (P.PD Bw.Kw) (Bw.rep r)) : ℤ) =
      (Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) : ℤ) -
        Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r) ⊓
          FilV (P.PD Bw.Kw) (LL := ↥Bw.LL.1) (V := Fin m → ↥Bw.LL.1) 0) := by
  have hG := (GlobalTheory.LocalIntegers.good_integers l Bw.LL).1
  let A := grepOf Bw r hr
  have hA : IsDR (P.PD Bw.Kw) A.ρ := by
    change Module.finrank ↥Bw.LL.1 ↥(DdR (P.PD Bw.Kw) (Bw.rep r)) =
      Module.finrank ℚ_[l] ↥Bw.Kw.1 * Module.finrank ↥Bw.LL.1 (Fin m → ↥Bw.LL.1)
    rw [Module.finrank_fin_fun]
    exact hdR
  have key := hBK _ _ hG A hA
  have h0 : Module.finrank ↥Bw.LL.1 ↥(H0V A.ρ) = 0 := by
    have : H0V A.ρ = ⊥ := localGaloisRep_invariants_from_fractionRing Bw r h
    rw [this, finrank_bot]
  rw [h0, Nat.cast_zero, zero_add] at key
  exact key

end Bridge

end GlobalTheory.BKDimNoInv
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.LowestWeightGeneratedFiltration
section
open Formalism.BasicNotions.TH GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.MatrixMinorProducts MeasureTheory
open Formalism.MainNotions.SchurIrreducible (IrrU IrrGK IsHCMod)
open scoped TensorProduct

noncomputable section
namespace GlobalTheory.FockGrade

variable {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]

theorem act_Eab_comm {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) (a b c d : Ix p q) (x : V) :
    act (Eab a b) (act (Eab c d) x) = act (Eab c d) (act (Eab a b) x) +
      (if b = c then act (Eab a d) x else 0) - (if d = a then act (Eab c b) x else 0) := by
  have h1 := congrArg (fun f : Module.End ℂ V => f x) (h (Eab a b) (Eab c d))
  simp only [map_sub, LinearMap.sub_apply, Module.End.mul_apply] at h1
  have e1 : act (Eab a b * Eab c d) x = if b = c then act (Eab a d) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  have e2 : act (Eab c d * Eab a b) x = if d = a then act (Eab c b) x else 0 := by
    split_ifs with hbc
    · subst hbc; simp [Eab, Matrix.single_mul_single_same]
    · simp [Eab, Matrix.single_mul_single_of_ne _ _ _ _ hbc]
  rw [← e1, ← e2, add_sub_assoc, h1]; abel

def layer (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) : Submodule ℂ V :=
  Nat.rec W (fun _ N => ⨆ ab : Fin p × Fin q, N.map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2)))) m

theorem layer_succ (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (W : Submodule ℂ V) (m : ℕ) :
    layer act W (m + 1) =
      ⨆ ab : Fin p × Fin q, (layer act W m).map (act (Eab (Sum.inl ab.1) (Sum.inr ab.2))) := rfl

theorem raise_mem {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} (a : Fin p) (b : Fin q)
    {y : V} (hy : y ∈ layer act W m) : act (Eab (Sum.inl a) (Sum.inr b)) y ∈ layer act W (m + 1) :=
  Submodule.mem_iSup_of_mem (a, b) (Submodule.mem_map_of_mem hy)

theorem layer_succ_le {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {m : ℕ} {S : Submodule ℂ V}
    (h : ∀ a b, ∀ y ∈ layer act W m, act (Eab (Sum.inl a) (Sum.inr b)) y ∈ S) : layer act W (m + 1) ≤ S := by
  refine iSup_le fun ab => ?_
  rintro _ ⟨y, hy, rfl⟩
  exact h _ _ y hy

theorem layer_finite {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} (hW : FiniteDimensional ℂ W)
    (m : ℕ) : FiniteDimensional ℂ (layer act W m) := by
  induction m with
  | zero => exact hW
  | succ m ih => rw [layer_succ]; infer_instance

theorem layer_compact {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (m : ℕ) : ∀ a b, sameBlock a b → ∀ y ∈ layer act W m,
      act (Eab a b) y ∈ layer act W m := by
  induction m with
  | zero => intro a b hab y hy; exact hK _ (GlobalTheory.FockTensor.isKC_Eab hab) y hy
  | succ m ih =>
    intro a b hab
    have : layer act W (m + 1) ≤ (layer act W (m + 1)).comap (act (Eab a b)) := by
      refine layer_succ_le fun i j y hy => ?_
      rw [Submodule.mem_comap, act_Eab_comm h]
      refine sub_mem (add_mem (raise_mem _ _ (ih a b hab y hy)) ?_) ?_
      · split_ifs with hb
        · subst hb
          rcases a with a | a
          · exact raise_mem _ _ hy
          · exact absurd hab (by simp [sameBlock])
        · exact zero_mem _
      · split_ifs with hb
        · subst hb
          rcases b with b | b
          · exact absurd hab (by simp [sameBlock])
          · exact raise_mem _ _ hy
        · exact zero_mem _
    exact fun y hy => this hy

theorem sup_stable_of {act : Mat p q →ₗ[ℂ] Module.End ℂ V} {W : Submodule ℂ V} {f : Module.End ℂ V}
    (hf : ∀ m, ∀ y ∈ layer act W m, f y ∈ ⨆ m, layer act W m) :
    ∀ y ∈ ⨆ m, layer act W m, f y ∈ ⨆ m, layer act W m := by
  have : (⨆ m, layer act W m) ≤ (⨆ m, layer act W m).comap f := iSup_le fun m y hy => hf m y hy
  exact fun y hy => this hy

theorem sup_stable {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V}
    (hK : KStable act W) (hL : ∀ e ∈ W, KilledByLower act e) (a b : Ix p q) :
    ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m := by
  have hk : ∀ a b, sameBlock a b → ∀ y ∈ ⨆ m, layer act W m, act (Eab a b) y ∈ ⨆ m, layer act W m :=
    fun a b hab => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem m (layer_compact h hK m a b hab y hy)
  have hr : ∀ a b, ∀ y ∈ ⨆ m, layer act W m,
      act (Eab (Sum.inl a) (Sum.inr b)) y ∈ ⨆ m, layer act W m :=
    fun a b => sup_stable_of fun m y hy => Submodule.mem_iSup_of_mem (m + 1) (raise_mem a b hy)
  rcases a with a | a <;> rcases b with b | b
  · exact hk _ _ trivial
  · exact hr _ _
  · refine sup_stable_of fun m => ?_
    induction m with
    | zero => intro y hy; rw [hL y hy b a]; exact zero_mem _
    | succ m ih =>
      have : layer act W (m + 1) ≤ (⨆ m, layer act W m).comap (act (Eab (Sum.inr a) (Sum.inl b))) := by
        refine layer_succ_le fun i j y hy => ?_
        have hy' : y ∈ ⨆ m, layer act W m := Submodule.mem_iSup_of_mem m hy
        rw [Submodule.mem_comap, act_Eab_comm h]
        refine sub_mem (add_mem (hr _ _ _ (ih y hy)) ?_) ?_
        · split_ifs
          · exact hk (Sum.inr a) (Sum.inr j) trivial _ hy'
          · exact zero_mem _
        · split_ifs
          · exact hk (Sum.inl i) (Sum.inl b) trivial _ hy'
          · exact zero_mem _
      exact fun y hy => this hy
  · exact hk _ _ trivial

theorem layer_eigen {act : Mat p q →ₗ[ℂ] Module.End ℂ V} (h : IsLieAct act) {W : Submodule ℂ V} {c : ℂ}
    (hc : ∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) (m : ℕ) :
    ∀ x ∈ layer act W m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  induction m with
  | zero => intro x hx; simpa using hc x hx
  | succ m ih =>
    have : layer act W (m + 1) ≤ LinearMap.ker ((∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i))) -
        (c + ((m + 1 : ℕ) : ℂ)) • (LinearMap.id : V →ₗ[ℂ] V)) := by
      refine layer_succ_le fun a b y hy => ?_
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero]
      have e : ∀ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) (act (Eab (Sum.inl a) (Sum.inr b)) y) =
          act (Eab (Sum.inl a) (Sum.inr b)) (act (Eab (Sum.inl i) (Sum.inl i)) y) +
            (if i = a then act (Eab (Sum.inl a) (Sum.inr b)) y else 0) := by
        intro i
        rw [act_Eab_comm h]
        by_cases hi : i = a
        · subst hi; simp
        · simp [hi]
      simp only [e, Finset.sum_add_distrib, ← map_sum, ih y hy]
      simp [add_smul, add_assoc]
    intro x hx
    have h2 := this hx
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.sum_apply, sub_eq_zero] at h2
    simpa using h2

theorem exists_grading : ∀ (p q : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V), IsLieAct act → ∀ (W : Submodule ℂ V) (c : ℂ), FiniteDimensional ℂ W → KStable act W → (∀ e ∈ W, KilledByLower act e) → (∀ e ∈ W, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) e = c • e) → ∃ N : ℕ → Submodule ℂ V, N 0 = W ∧ (∀ m, FiniteDimensional ℂ (N m)) ∧ (⨆ m, N m) = genSub act (W : Set V) ∧ ∀ m : ℕ, ∀ x ∈ N m, ∑ i : Fin p, act (Eab (Sum.inl i) (Sum.inl i)) x = (c + m) • x := by
  intro p q V _ _ act h W c hW hK hL hc
  refine ⟨layer act W, rfl, layer_finite hW, le_antisymm ?_ ?_, layer_eigen h hc⟩
  · refine iSup_le fun m => le_sInf fun S hS => ?_
    induction m with
    | zero => exact hS.1
    | succ m ih => exact layer_succ_le fun a b y hy => hS.2 _ _ (ih hy)
  · refine sInf_le ⟨fun x hx => Submodule.mem_iSup_of_mem 0 hx, fun Z y hy => ?_⟩
    have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
      conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
      simp [Eab, Matrix.smul_single]
    rw [hZ]
    simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply]
    exact Submodule.sum_mem _ fun a _ => Submodule.sum_mem _ fun b _ =>
      Submodule.smul_mem _ _ (sup_stable h hK hL a b y hy)

end GlobalTheory.FockGrade
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.NatCastPowNeZero
section
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.BlochKatoReduction GlobalTheory.IndefiniteRowSideFullHecke.LengthValuationTwists

namespace GlobalTheory.BlochKatoRank

theorem rank_subquotient_eq {O K X Y : Type} [CommRing O] [IsDomain O] [Field K] [Algebra O K]
    [IsFractionRing O K] [AddCommGroup X] [Module O X] [AddCommGroup Y] [Module K Y] [Module O Y]
    [IsScalarTower O K Y] (φ : X →ₗ[O] Y) (Z B A : Submodule O X) (Zf BV : Submodule K Y)
    (h1 : ∀ a ∈ A, φ a ∈ Zf) (h2 : ∀ b ∈ B, φ b ∈ BV)
    (h3 : ∀ a, φ a ∈ BV → ∃ m : O, m ≠ 0 ∧ m • a ∈ B)
    (h4 : ∀ y ∈ Zf, ∃ m : O, m ≠ 0 ∧ ∃ a ∈ Z, a ∈ A ∧ φ a = m • y) :
    Module.rank O ((A.comap Z.subtype).map (Submodule.mkQ (B.comap Z.subtype))) =
      Module.rank K (Zf ⧸ BV.comap Zf.subtype) := by
  let A' := A.comap Z.subtype
  let g : A' →ₗ[O] (Z ⧸ B.comap Z.subtype) := (Submodule.mkQ _).comp A'.subtype
  have hg : LinearMap.range g = A'.map (Submodule.mkQ (B.comap Z.subtype)) := by
    rw [LinearMap.range_comp, Submodule.range_subtype]
  let f0 : A' →ₗ[O] Zf :=
    { toFun := fun a => ⟨φ a.1.1, h1 _ a.2⟩
      map_add' := fun a b => Subtype.ext (by simp)
      map_smul' := fun c a => Subtype.ext (by simp) }
  let f : A' →ₗ[O] (Zf ⧸ BV.comap Zf.subtype) :=
    ((Submodule.mkQ (BV.comap Zf.subtype)).restrictScalars O).comp f0
  have hgk : ∀ a : A', g a = 0 ↔ a.1.1 ∈ B := fun a => Submodule.Quotient.mk_eq_zero _
  have hfk : ∀ a : A', f a = 0 ↔ φ a.1.1 ∈ BV := fun a => Submodule.Quotient.mk_eq_zero _
  have hle : LinearMap.ker g ≤ LinearMap.ker f := fun a ha =>
    (hfk a).2 (h2 _ ((hgk a).1 ha))
  let F := (LinearMap.ker g).liftQ f hle
  haveI : IsLocalizedModule (nonZeroDivisors O) F := by
    refine ⟨fun s => ?_, fun y => ?_, fun {x y} h => ?_⟩
    · have hs : algebraMap O K s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
      rw [Module.End.isUnit_iff]
      refine ⟨fun a b h => ?_, fun a => ⟨(algebraMap O K s)⁻¹ • a, ?_⟩⟩
      · simp only [Module.algebraMap_end_apply] at h
        rw [← algebraMap_smul K, ← algebraMap_smul K (s : O) b] at h
        exact smul_right_injective _ hs h
      · rw [Module.algebraMap_end_apply, ← algebraMap_smul K, smul_inv_smul₀ hs]
    · obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ y
      obtain ⟨m, hm, a, haZ, haA, ha⟩ := h4 y.1 y.2
      refine ⟨(Submodule.Quotient.mk ⟨⟨a, haZ⟩, haA⟩, ⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩), ?_⟩
      have : f0 ⟨⟨a, haZ⟩, haA⟩ = m • y := Subtype.ext ha
      change m • ((BV.comap Zf.subtype).mkQ.restrictScalars O) y =
        ((BV.comap Zf.subtype).mkQ.restrictScalars O) (f0 ⟨⟨a, haZ⟩, haA⟩)
      rw [this, map_smul]
    · rw [← sub_eq_zero, ← map_sub] at h
      suffices H : ∃ m : O, m ≠ 0 ∧ m • (x - y) = 0 by
        obtain ⟨m, hm, H⟩ := H
        exact ⟨⟨m, mem_nonZeroDivisors_of_ne_zero hm⟩, by
          rw [smul_sub, sub_eq_zero] at H; exact H⟩
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x - y)
      rw [← ha] at h ⊢
      obtain ⟨m, hm, H⟩ := h3 _ ((hfk a).1 h)
      refine ⟨m, hm, ?_⟩
      rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]
      exact (hgk _).2 H
  rw [← hg, ← (LinearMap.quotKerEquivRange g).rank_eq,
    IsLocalization.rank_eq K (nonZeroDivisors O) le_rfl,
    IsLocalizedModule.rank_eq (nonZeroDivisors O) le_rfl F]

section Bridge

open GlobalTheory.BlochKatoIntegralScalars

variable {l : ℕ} [Fact l.Prime] {E Ω : Type} [Field E] [Field Ω] [Algebra E Ω]
  {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O₀ : Type} [CommRing O₀] [Algebra ℤ_[l] O₀] [TopologicalSpace O₀]
  (Bw : LocBridge l E Ω Gw O₀) (P : LocPrime l) {m : ℕ}

include Bw in
theorem natCast_pow_ne_zero (N : ℕ) : (l : O₀) ^ N ≠ 0 := by
  intro h
  have := congrArg Bw.toLL h
  rw [map_pow, map_natCast, map_zero] at this
  exact (Fact.out : l.Prime).ne_zero (by exact_mod_cast (eq_zero_of_pow_eq_zero this))

theorem exists_integral {X : Type} [TopologicalSpace X] [CompactSpace X]
    (c : X → Fin m → ↥Bw.LL.1) (hc : Continuous c) :
    ∃ d : O₀, d ≠ 0 ∧ ∃ f : X → Fin m → O₀, Continuous f ∧
      ∀ g j, Bw.toLL (f g j) = Bw.toLL d * c g j := by
  obtain ⟨N, hN⟩ := exists_pow_mul_mem_OL Bw.LL c hc
  refine ⟨(l : O₀) ^ N, natCast_pow_ne_zero Bw N, fun g j => Bw.eO.symm ⟨_, hN g j⟩, ?_, ?_⟩
  · refine continuous_pi fun j => Bw.eO_symm_cont.comp ?_
    exact Continuous.subtype_mk (continuous_const.mul ((continuous_apply j).comp hc)) _
  · intro g j
    show ((Bw.eO (Bw.eO.symm _) : Loc.OL Bw.LL) : Bw.LL.1) = _
    rw [RingEquiv.apply_symm_apply, map_pow, map_natCast]

end Bridge

end GlobalTheory.BlochKatoRank
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SemisimpleTensorOfSemisimplePotentials
section
noncomputable section

open scoped MatrixGroups TensorProduct
open Matrix GlobalTheory.KZ

namespace GlobalTheory.KZ.Comp

theorem lift_mem_lam {Ω : Type} [Field Ω] [Algebra ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε) (N l : ℕ) [Fact l.Prime]
    {E : Type} [Field E] [Algebra ℤ_[l] E] (P : FreeAlgebra E Letter) :
    ∀ p ∈ H3.abelian₂ X l E,
      (FreeAlgebra.lift E (X.opV N l E) P p.1, FreeAlgebra.lift E (opL E N l) P p.2) ∈ H3.abelian₂ X l E := by
  induction P using FreeAlgebra.induction with
  | grade0 r =>
    intro p hp
    convert (H3.abelian₂ X l E).smul_mem r hp using 1
    ext <;> simp [Algebra.algebraMap_eq_smul_one]
  | grade1 T =>
    intro p hp
    simpa using GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T p hp
  | mul a b ha hb =>
    intro p hp
    simpa using ha _ (hb p hp)
  | add a b ha hb =>
    intro p hp
    simpa using (H3.abelian₂ X l E).add_mem (ha p hp) (hb p hp)

theorem ssbb_of_ssPotB : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : Tower Ω ε), Function.Injective ε → (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) → ∀ (N l w : ℕ) [Fact l.Prime], l ≠ 2 → 5 ≤ N → Nat.Coprime N l → Odd w → ∀ {E : Type} [Field E] [Algebra ℤ_[l] E] (ι : E ≃+* ℂ) (lam : Letter → E), SSPotB N l w (fun T => ι (lam T)) → X.SSBB N l w E lam := by
  intro Ω _ _ _ ε X hε hj N l w _ hl2 hN hNl hw E _ _ ι lam hSS
  haveI : CharZero E := RingHom.charZero ι.toRingHom
  obtain ⟨P, hPA, hP1, hP⟩ := GlobalTheory.T.semisimpleHeckePoly_transport_ringEquiv N l w ι lam hSS
  refine ⟨P, hPA, hP1, fun x hx T hT => ?_⟩
  obtain ⟨G, hG, hxG⟩ := GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_VB ε X N l w (GlobalTheory.T.exists_eichlerShimuraPotential_of_mem_kummer ε X hε hj N l w hl2 hN hNl hw) x hx
  have h1 := lift_mem_lam ε X N l P (x, G) hxG
  have h2 := GlobalTheory.T.kummerPotentialSpan_hecke_letter_stable ε X N l T _ h1
  have h3 := (H3.abelian₂ X l E).sub_mem h2 ((H3.abelian₂ X l E).smul_mem (lam T) h1)
  have h4 : ((X.opV N l E T - lam T • (1 : Module.End E (E ⊗[ℤ_[l]] X.Fn l)))
        (FreeAlgebra.lift E (X.opV N l E) P x),
      (opL E N l T - lam T • (1 : Module.End E (ℂ → MvPolynomial (Fin 2) E)))
        (FreeAlgebra.lift E (opL E N l) P G)) ∈ H3.abelian₂ X l E := by
    simpa using h3
  exact GlobalTheory.T.kummerRelatedPair_fst_eq_zero_of_trivial ε X hε hj N l w (by omega) inferInstance _ _ h4 (hP G hG T hT)

end GlobalTheory.KZ.Comp
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumSlashHeckeRepLowerHeckeVEigenformStatement
section
open UpperHalfPlane Complex MeasureTheory CongruenceSubgroup GlobalTheory.EisM UpperTheory.V.Af Filter Topology
open scoped MatrixGroups Real ComplexConjugate Manifold ModularForm
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.sum_slash_heckeRepLower_heckeV_eigenform : ∀ (k N l : ℕ) (ε : DirichletCharacter ℂ N) (h : ℕ → ℂ) (t : ℂ), 1 ≤ k → 0 < N → l.Prime → ¬ l ∣ N → MF k N (ch ε) h → To k (ch ε l) l h = t • h → ∀ τ : ℍ, ∑ j : Fin l, slz k (repL (N * l) l (some j)) (qs (Vo l h)) τ = ch ε⁻¹ l * (t * qs (Vo l h) τ - (l : ℂ)⁻¹ * qs h τ) := by
  first | exact @GlobalTheory.EisM.sum_slz_repL_Vo | exact GlobalTheory.EisM.sum_slz_repL_Vo | (intros; apply GlobalTheory.EisM.sum_slz_repL_Vo <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.TqFSemisimple
section
open GlobalTheory.HeckeFamilyMatrices Polynomial UpperHalfPlane
open scoped MatrixGroups ModularForm
open scoped Manifold

namespace GlobalTheory.HeckeFamilyMatrices

theorem tqF_semisimple : ∀ (N l k : ℕ), 5 ≤ N → l.Prime → ¬ l ∣ N → 3 ≤ k → ∀ (q : ℕ) (σ : SL(2, ℤ)), q.Prime → ¬ q ∣ N * l → IsDiam N l (q : ZMod N) σ →
  ∀ (f : CuspForm (Lev N l) (k : ℤ)) (c : ℂ) (n : ℕ), (fun F => TqF (k : ℤ) q σ F - c • F)^[n] ⇑f = 0 → TqF (k : ℤ) q σ ⇑f = c • ⇑f := by
  intro N l k hN hl hlN hk q σ hq hqNl hσ f c n hf
  obtain ⟨_, _, hT, hD, _⟩ := GlobalTheory.T.heckeOperatorsOnHalfPlaneFunctions_agree_explicit
  have hq0 : 0 < q := hq.pos
  have hfun : (fun F => TqF (k : ℤ) q σ F - c • F) = (fun h => GlobalTheory.Hk.heckeT (k:ℤ) q σ h - c • h) := by
    funext F; rw [hT _ _ _ _ hq0]
  have hσ' : GlobalTheory.Hk.IsDia N l ((q:ℕ):ℤ) σ := (hD N l q σ).1 (by simpa using hσ)
  rw [hfun] at hf
  rw [hT _ _ _ _ hq0]
  exact GlobalTheory.T.heckeTOperatorExplicit_semisimple_cuspForms N l q k σ c n (by omega) hl.pos hq hqNl hσ' f hf

end GlobalTheory.HeckeFamilyMatrices
end

-- bundled from Development.AbelianVarietyTheory.Proofs.FoundationProofs.WeightComponentMem
section
namespace GlobalTheory.WeightSubspaceComponent

open Formalism.BasicNotions.TH

theorem mem_wtSub_iff {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (x : V) :
    x ∈ wtSub act μ ↔ ∀ a, act (Eab a a) x = ((μ a : ℚ) : ℂ) • x := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
    LinearMap.id_apply, sub_eq_zero]

theorem weight_component_mem {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (act : Mat p q →ₗ[ℂ] Module.End ℂ V) (N : Submodule ℂ V)
    (hN : ∀ (a : Ix p q), ∀ x ∈ N, act (Eab a a) x ∈ N)
    (S : Finset (Ix p q → ℚ)) (f : (Ix p q → ℚ) → V)
    (hf : ∀ ν, f ν ∈ wtSub act ν) (hS : ∑ ν ∈ S, f ν ∈ N) : ∀ ν ∈ S, f ν ∈ N := by
  classical
  induction S using Finset.strongInduction generalizing f with
  | H S ih =>
    intro ν hν
    by_cases h : ∃ μ ∈ S, μ ≠ ν
    · obtain ⟨μ, hμ, hne⟩ := h
      obtain ⟨a, ha⟩ := Function.ne_iff.mp hne
      let g : (Ix p q → ℚ) → V := fun l => (((l a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) • f l
      have hg : ∀ l, g l ∈ wtSub act l := fun l => Submodule.smul_mem _ _ (hf l)
      have hsum : ∑ l ∈ S.erase μ, g l
          = act (Eab a a) (∑ l ∈ S, f l) - ((μ a : ℚ) : ℂ) • ∑ l ∈ S, f l := by
        rw [Finset.sum_erase S (by simp [g]), map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
        refine Finset.sum_congr rfl fun l _ => ?_
        rw [(mem_wtSub_iff act l (f l)).mp (hf l) a]
        exact sub_smul _ _ _
      have hmem : ∑ l ∈ S.erase μ, g l ∈ N := by
        rw [hsum]
        exact N.sub_mem (hN a _ hS) (N.smul_mem _ hS)
      have hgν := ih (S.erase μ) (Finset.erase_ssubset hμ) g hg hmem ν
        (Finset.mem_erase.mpr ⟨hne.symm, hν⟩)
      have hc : (((ν a : ℚ) : ℂ) - ((μ a : ℚ) : ℂ)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast ha.symm
      exact (N.smul_mem_iff hc).mp hgν
    · have hone : ∑ l ∈ S, f l = f ν :=
        Finset.sum_eq_single_of_mem ν hν fun μ hμ hne => absurd ⟨μ, hμ, hne⟩ h
      rwa [hone] at hS

end GlobalTheory.WeightSubspaceComponent
end

