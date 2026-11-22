import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.FiniteCohPushforwardIffOfIsClosedImmersion
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.CechModulesFunctorShortExactOfIsAffineOpen
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0252
import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0936
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle1041
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThird
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0044
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsMultiHomogeneousFixFirstBlock
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChowFormIntExistsAndChowFormExists
import Development.AbelianVarietyTheory.Definitions.QuasicoherentCohomology.AlgebraMapBaseMemMaximalIdealIff
import ReciprocityTheory.SemistableReduction.Bundle0004
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HilbertDegreeEqSumOverComponents

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelOfPresents
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.Cartier.Presents

variable {X : Scheme.{0}} [IsIntegral X] {D : CartierDiv X} {L : LB X} {r : L.ι → X.functionFieldˣ}

def genChart (h : Presents D L r) : L.ι := (exists_chart h.isLB (genericPoint X)).choose

theorem gen_mem_genChart (h : Presents D L r) : genericPoint X ∈ L.U h.genChart :=
  (exists_chart h.isLB (genericPoint X)).choose_spec

def secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) : Γ(LB.toMod L, U) →+ X.functionField :=
  AddMonoidHom.mk' (fun s => fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField)) fun s t => by
    rw [LB.coord_add, map_add, add_div]

theorem secVal_apply (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U)) :
    h.secVal U hU s = fnOf _ (memInf hU h.gen_mem_genChart) (LB.coord s h.genChart) /
      (r h.genChart : X.functionField) := rfl

theorem secVal_mul (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (s : Γ(LB.toMod L, U))
    (i : L.ι) (hi : genericPoint X ∈ U ⊓ L.U i) :
    h.secVal U hU s * r i = fnOf _ hi (LB.coord s i) := by
  have h₀ := h.gen_mem_genChart
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U h.genChart := ⟨hi, h₀⟩
  have e := congrArg (fnOf _ hW) (LB.coord_rel s i h.genChart
    (inf_le_left : U ⊓ L.U i ⊓ L.U h.genChart ≤ U ⊓ L.U i)
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right)
    (le_inf (inf_le_left.trans inf_le_right) inf_le_right))
  rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG] at e
  rw [e, secVal_apply, h.isRatSec i h.genChart (memInf hi.2 h₀), mul_left_comm]
  exact congrArg _ (div_mul_cancel₀ _ (Units.ne_zero _))

theorem secVal_injective (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) :
    Function.Injective (h.secVal U hU) := fun s t e =>
  LB.sec_ext fun i => fn_ext fun hi => by rw [← h.secVal_mul U hU s i hi, ← h.secVal_mul U hU t i hi, e]

theorem mem_range_secVal (h : Presents D L r) (U : X.Opens) (hU : genericPoint X ∈ U) (f : X.functionField) :
    f ∈ (h.secVal U hU).range ↔ ∀ y ∈ U, D.RegularAt y f := by
  constructor
  · rintro ⟨s, rfl⟩ y hy
    obtain ⟨i, hi⟩ := exists_chart h.isLB y
    have hyi : y ∈ U ⊓ L.U i := ⟨hy, hi⟩
    refine (h.isEqn i y hi).regularAt_iff.2 ?_
    rw [h.secVal_mul U hU s i (gen_mem hyi)]
    exact regAt_fnOf hyi _ _
  · intro hf
    have key (i : L.ι) : ∃ a : Γ(X, U ⊓ L.U i), ∀ hi, fnOf _ hi a = f * r i := by
      by_cases hi : genericPoint X ∈ U ⊓ L.U i
      · obtain ⟨a, ha⟩ := exists_fnOf_eq hi fun x hx =>
          (h.isEqn i x hx.2).regularAt_iff.1 (hf x hx.1)
        exact ⟨a, fun _ => ha⟩
      · exact ⟨0, fun h' => (hi h').elim⟩
    choose a ha using key
    have hmem : a ∈ secOn L U := fun i j => fn_ext fun hij => by
      rw [map_mul, fnOf_resG, fnOf_resG, fnOf_resG, ha, ha,
        h.isRatSec i j (memInf hij.1.2 hij.2), mul_left_comm]
    refine ⟨LB.mkSec a hmem, ?_⟩
    rw [secVal_apply, LB.coord_mkSec, ha]
    exact mul_div_cancel_right₀ _ (Units.ne_zero _)

def latModel (h : Presents D L r) :
    LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L) where
  val := h.secVal
  inj := h.secVal_injective
  range U hU := by
    ext f
    rw [h.mem_range_secVal U hU f]
    simp only [latSec, AddSubgroup.mem_iInf, Submodule.mem_toAddSubgroup, CartierDiv.mem_secOn,
      Set.mem_singleton_iff, forall_eq]
  res U W e hW s := by
    rw [secVal_apply, secVal_apply, LB.coord_map, fnOf_resG]
  smul U hU a s := by
    rw [secVal_apply, secVal_apply, LB.coord_smul, map_mul, fnOf_resG, smul_eq_mul, mul_div_assoc]

end GlobalTheory.Cartier.Presents

theorem GlobalTheory.Cartier.nonempty_latModel_of_presents : ∀ (X : Scheme.{0}) [IsIntegral X] (D : CartierDiv X) (L : LB X)
    (r : L.ι → X.functionFieldˣ), Presents D L r →
    Nonempty (LatModel (V := X.functionField) (fun y => (D.secOn {y}).toAddSubgroup) (LB.toMod L)) :=
  fun _ _ _ _ _ h => ⟨h.latModel⟩
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonemptyLatModelTwist
section
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.LogDR

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {L : LB X} {r : L.ι → X.functionFieldˣ}

theorem sec_eq_of_not_gen {W : X.Opens} (hW : genericPoint X ∉ W) (s t : Γ(F, W)) : s = t :=
  sec_ext_of_cover (ι := PEmpty.{1}) (fun k => k.elim) (fun k => k.elim)
    (by intro x hx; exact (hW (gen_mem hx)).elim) (fun k => k.elim)

theorem val_resM (hM : LatModel M F) {U W : X.Opens} (e : W ≤ U) (h : genericPoint X ∈ W)
    (s : Γ(F, U)) : hM.val W h (resM F e s) = hM.val U (e h) s :=
  hM.res U W e h s

variable (r) in

def tval (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) : Γ(twist F L, U) →+ V where
  toFun s := (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i)
  map_zero' := by rw [coord_zero, map_zero, smul_zero]
  map_add' s t := by rw [coord_add, map_add, smul_add]

theorem tval_apply (hM : LatModel M F) (i : L.ι) (hi : genericPoint X ∈ L.U i) (U : X.Opens)
    (h : genericPoint X ∈ U) (s : Γ(twist F L, U)) :
    tval r hM i hi U h s = (r i)⁻¹ • hM.val (U ⊓ L.U i) (memInf h hi) (coord s i) := rfl

theorem val_coord_rel (hM : LatModel M F) {U : X.Opens} (s : Γ(twist F L, U)) (i j : L.ι)
    (hU : genericPoint X ∈ U) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j) :
    hM.val (U ⊓ L.U i) (memInf hU hi) (coord s i) =
      fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) •
        hM.val (U ⊓ L.U j) (memInf hU hj) (coord s j) := by
  have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := memInf (memInf hU hi) hj
  have e := coord_rel s i j (W := U ⊓ L.U i ⊓ L.U j) inf_le_left
    (le_inf (inf_le_left.trans inf_le_left) inf_le_right) (inf_le_inf_right _ inf_le_right)
  have e1 := val_resM hM (inf_le_left : U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U i) hW (coord s i)
  have e2 := val_resM hM (le_inf (inf_le_left.trans inf_le_left) inf_le_right :
    U ⊓ L.U i ⊓ L.U j ≤ U ⊓ L.U j) hW (coord s j)
  rw [← e1, ← e2, e, hM.smul, fnOf_resG]

theorem tval_eq (hM : LatModel M F) (hr : IsRatSec L r) {U : X.Opens} (h : genericPoint X ∈ U)
    (i j : L.ι) (hi : genericPoint X ∈ L.U i) (hj : genericPoint X ∈ L.U j)
    (s : Γ(twist F L, U)) : tval r hM i hi U h s = tval r hM j hj U h s := by
  rw [tval_apply, tval_apply, val_coord_rel hM s i j h hi hj, Units.smul_def, Units.smul_def,
    smul_smul, Units.val_inv_eq_inv_val, Units.val_inv_eq_inv_val, hr i j (memInf hi hj)]
  congr 1
  have hg : fnOf (L.U i ⊓ L.U j) (memInf hi hj) (L.g i j : Γ(X, L.U i ⊓ L.U j)) ≠ 0 :=
    ((L.g i j).isUnit.map (fnOf (L.U i ⊓ L.U j) (memInf hi hj))).ne_zero
  have hrj : (r j : X.functionField) ≠ 0 := (r j).ne_zero
  field_simp

end LatTwist

end GlobalTheory.LogDR

namespace GlobalTheory.LogDR

namespace LatTwist

open GlobalTheory.Twist

variable {X : Scheme.{0}} [IsIntegral X] {V : Type} [AddCommGroup V] [Module X.functionField V]
  {M M' : X → AddSubgroup V} {F : X.Modules} {D : CartierDiv X} {L : LB X}
  {r : L.ι → X.functionFieldˣ}

theorem mem_of_mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : v ∈ latSec N U)
    {y : X} (hy : y ∈ U) : v ∈ N y :=
  AddSubgroup.mem_iInf.1 (AddSubgroup.mem_iInf.1 hv y) hy

theorem mem_latSec {N : X → AddSubgroup V} {U : X.Opens} {v : V} (hv : ∀ y ∈ U, v ∈ N y) :
    v ∈ latSec N U :=
  AddSubgroup.mem_iInf.2 fun y => AddSubgroup.mem_iInf.2 fun hy => hv y hy

def twistModel (hP : Presents D L r)
    (hE : ∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y))
    (hM : LatModel M F) (i₀ : L.ι) (hi₀ : genericPoint X ∈ L.U i₀) :
    LatModel M' (twist F L) where
  val U h := tval r hM i₀ hi₀ U h
  inj U h := by
    intro s t e
    refine sec_ext fun i => ?_
    by_cases hi : genericPoint X ∈ L.U i
    · have e' : tval r hM i hi U h s = tval r hM i hi U h t := by
        rw [← tval_eq hM hP.isRatSec h i₀ i hi₀ hi, ← tval_eq hM hP.isRatSec h i₀ i hi₀ hi]
        exact e
      rw [tval_apply, tval_apply] at e'
      exact hM.inj (U ⊓ L.U i) (memInf h hi) (MulAction.injective _ e')
    · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i => hi hh.2) _ _
  range U h := by
    ext v
    rw [AddMonoidHom.mem_range]
    constructor
    · rintro ⟨s, rfl⟩
      refine mem_latSec fun y hy => ?_
      obtain ⟨i, hi⟩ := exists_chart hP.isLB y
      have hgi : genericPoint X ∈ L.U i := gen_mem hi
      rw [tval_eq hM hP.isRatSec h i₀ i hi₀ hgi, hE y (r i) _ (hP.isEqn i y hi), tval_apply,
        ← Units.smul_def, smul_inv_smul]
      have hw : hM.val (U ⊓ L.U i) (memInf h hgi) (coord s i) ∈ (hM.val (U ⊓ L.U i) (memInf h hgi)).range :=
        AddMonoidHom.mem_range.2 ⟨_, rfl⟩
      rw [hM.range] at hw
      exact mem_of_mem_latSec hw (memInf hy hi)
    · intro hv
      have key : ∀ i, ∃ t : Γ(F, U ⊓ L.U i),
          ∀ hi : genericPoint X ∈ L.U i, hM.val (U ⊓ L.U i) (memInf h hi) t = r i • v := by
        intro i
        by_cases hi : genericPoint X ∈ L.U i
        · have hm : r i • v ∈ latSec M (U ⊓ L.U i) := mem_latSec fun y hy => by
            rw [Units.smul_def, ← hE y (r i) v (hP.isEqn i y hy.2)]
            exact mem_of_mem_latSec hv hy.1
          rw [← hM.range (U ⊓ L.U i) (memInf h hi)] at hm
          obtain ⟨t, ht⟩ := hm
          exact ⟨t, fun _ => ht⟩
        · exact ⟨0, fun h' => (hi h').elim⟩
      choose t ht using key
      have hmem : t ∈ Twist.secGroup F L U := by
        intro i j
        by_cases hij : genericPoint X ∈ L.U i ⊓ L.U j
        · have hW : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j := (memInf (memInf h hij.1) hij.2)
          apply hM.inj (U ⊓ L.U i ⊓ L.U j) hW
          rw [hM.smul, val_resM, val_resM, fnOf_resG, ht i hij.1, ht j hij.2, Units.smul_def,
            Units.smul_def, smul_smul, hP.isRatSec i j hij]
        · exact sec_eq_of_not_gen (fun hh : genericPoint X ∈ U ⊓ L.U i ⊓ L.U j => hij (memInf hh.1.2 hh.2)) _ _
      exact ⟨mkSec t hmem, by rw [tval_apply, coord_mkSec, ht i₀ hi₀, inv_smul_smul]⟩
  res U W e h s := by
    change tval r hM i₀ hi₀ W h (resM (twist F L) e s) = tval r hM i₀ hi₀ U (e h) s
    rw [tval_apply, tval_apply, coord_resM, val_resM]
  smul U h a s := by
    change tval r hM i₀ hi₀ U h (a • s) = fnOf U h a • tval r hM i₀ hi₀ U h s
    rw [tval_apply, tval_apply, coord_smul, hM.smul, fnOf_resG, Units.smul_def, Units.smul_def,
      smul_smul, smul_smul, mul_comm]

end LatTwist

theorem nonempty_latModel_twist : ∀ (X : Scheme.{0}) [IsIntegral X] {V : Type} [AddCommGroup V]
    [Module X.functionField V] (M M' : X → AddSubgroup V) (F : X.Modules) (D : CartierDiv X)
    (L : LB X) (r : L.ι → X.functionFieldˣ), Presents D L r →
    (∀ y (g : X.functionFieldˣ) (v : V), D.IsEqn y g → (v ∈ M' y ↔ (g : X.functionField) • v ∈ M y)) →
    LatModel M F → Nonempty (LatModel M' (twist F L)) := by
  intro X _ V _ _ M M' F D L r hP hE hM
  obtain ⟨i₀, hi₀⟩ := exists_chart hP.isLB (genericPoint X)
  exact ⟨LatTwist.twistModel hP hE hM i₀ hi₀⟩

end GlobalTheory.LogDR
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonzeroEquivariantPairingHasForm
section
noncomputable section

open MvPolynomial Formalism.BasicNotions.TH GlobalTheory.CharPair
open scoped TensorProduct

namespace GlobalTheory.FockSplit

def jR (P Q R S : ℕ) : Ln P Q R 0 → Ln P Q R S := fun v => (v.1, Sum.elim Sum.inl (fun e => e.elim0) v.2)

def jS (P Q R S : ℕ) : Ln P Q 0 S → Ln P Q R S := fun v => (v.1, Sum.elim (fun e => e.elim0) Sum.inr v.2)

variable {P Q R S : ℕ}

theorem jR_injective : Function.Injective (jR P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · simp only [jR, Sum.elim_inl, Prod.mk.injEq, Sum.inl.injEq] at h; rw [h.1, h.2]
  · exact c'.elim0
  · exact c.elim0
  · exact c.elim0

theorem jS_injective : Function.Injective (jS P Q R S) := by
  rintro ⟨a, c | c⟩ ⟨a', c' | c'⟩ h
  · exact c.elim0
  · exact c.elim0
  · exact c'.elim0
  · simp only [jS, Sum.elim_inr, Prod.mk.injEq, Sum.inr.injEq] at h; rw [h.1, h.2]

theorem linePos_jR (l : Ln P Q R 0) : linePos (jR P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem linePos_jS (l : Ln P Q 0 S) : linePos (jS P Q R S l) = linePos l := by
  rcases l with ⟨a | a, c | c⟩ <;> first | exact c.elim0 | rfl

theorem jR_ne_jS (k : Ln P Q R 0) (m : Ln P Q 0 S) : jR P Q R S k ≠ jS P Q R S m := by
  rcases k with ⟨a, c | c⟩ <;> rcases m with ⟨a', e | e⟩
  · exact e.elim0
  · simp [jR, jS]
  · exact c.elim0
  · exact c.elim0

section General

variable {R' S' : ℕ} (j : Ln P Q R' S' → Ln P Q R S)

theorem pderiv_rename_eq_zero {σ τ : Type*} (i : σ → τ) (v : τ) (hv : ∀ m, i m ≠ v) (g : MvPolynomial σ ℂ) :
    pderiv v (rename i g) = 0 := by
  induction g using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p m hp => simp [hp, pderiv_X, Pi.single_apply, hv m]

theorem pderiv_rename_mul (hj : Function.Injective j) (k : Ln P Q R' S') (f : Pol P Q R' S') (G : Pol P Q R S)
    (hG : pderiv (j k) G = 0) : pderiv (j k) (rename j f * G) = rename j (pderiv k f) * G := by
  rw [Derivation.leibniz, hG, smul_zero, zero_add, pderiv_rename hj, smul_eq_mul, mul_comm]

theorem raiB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    raiB (j l) (rename j f * G) = rename j (raiB l f) * G := by
  unfold raiB; rw [hpos l]
  split_ifs
  · simp [mul_assoc]
  · simp [pderiv_rename_mul j hj l f G (hG l)]

theorem lowB_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    lowB (j l) (rename j f * G) = rename j (lowB l f) * G := by
  unfold lowB; rw [hpos l]
  split_ifs
  · simp [pderiv_rename_mul j hj l f G (hG l)]
  · simp [mul_assoc]

theorem omE_rename_mul (hj : Function.Injective j) (hpos : ∀ l, linePos (j l) = linePos l) (l l' : Ln P Q R' S')
    (f : Pol P Q R' S') (G : Pol P Q R S) (hG : ∀ k, pderiv (j k) G = 0) :
    omE (j l) (j l') (rename j f * G) = rename j (omE l l' f) * G := by
  simp only [omE, LinearMap.add_apply, Module.End.mul_apply, lowB_rename_mul j hj hpos l' f G hG,
    raiB_rename_mul j hj hpos l _ G hG, hj.eq_iff]
  split_ifs <;> simp [add_mul, smul_mul_assoc]

end General

theorem fockAct1_Eab_mul (a b : Ix P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S (Eab a b) (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 (Eab a b) f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S (Eab a b) g) := by
  rw [fockAct1_Eab, fockAct1_Eab, fockAct1_Eab]
  simp only [LinearMap.sum_apply, LinearMap.add_apply, Fintype.sum_sum_type, Finset.univ_eq_empty, Finset.sum_empty, add_zero, zero_add,
    map_sum, Finset.sum_mul, Finset.mul_sum]
  congr 1
  · refine Finset.sum_congr rfl fun c _ => ?_
    exact omE_rename_mul (jR P Q R S) jR_injective linePos_jR (a, .inl c) (b, .inl c) f _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => (jR_ne_jS k m).symm) g)
  · refine Finset.sum_congr rfl fun c _ => ?_
    rw [mul_comm, mul_comm (rename _ f)]
    exact omE_rename_mul (jS P Q R S) jS_injective linePos_jS (a, .inr c) (b, .inr c) g _
      (fun k => pderiv_rename_eq_zero _ _ (fun m => jR_ne_jS m k) f)

end GlobalTheory.FockSplit

namespace GlobalTheory.FockSplit

variable {P Q R S : ℕ}

theorem fockAct1_rename_mul (Z : Mat P Q) (f : Pol P Q R 0) (g : Pol P Q 0 S) :
    fockAct1 P Q R S Z (rename (jR P Q R S) f * rename (jS P Q R S) g) =
      rename (jR P Q R S) (fockAct1 P Q R 0 Z f) * rename (jS P Q R S) g +
        rename (jR P Q R S) f * rename (jS P Q R S) (fockAct1 P Q 0 S Z g) := by
  have hZ : Z = ∑ a, ∑ b, Z a b • Eab a b := by
    conv_lhs => rw [Matrix.matrix_eq_sum_single Z]
    simp only [Eab, Matrix.smul_single, smul_eq_mul, mul_one]
  rw [hZ]
  simp only [map_sum, map_smul, LinearMap.sum_apply, LinearMap.smul_apply, fockAct1_Eab_mul, smul_add,
    Finset.sum_add_distrib, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]

def toTens (P Q R S : ℕ) (v : Ln P Q R S) : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S :=
  Sum.elim (fun c => X (v.1, Sum.inl c) ⊗ₜ 1) (fun e => 1 ⊗ₜ X (v.1, Sum.inr e)) v.2

theorem hasForm_of_pairing : ∀ (P Q R S : ℕ) (x : ℚ) (b : Pol P Q R 0 →ₗ[ℂ] Pol P Q 0 S →ₗ[ℂ] ℂ), b ≠ 0 →
    (∀ Z f g, b (fockAct1 P Q R 0 Z f) g + b f (fockAct1 P Q 0 S Z g) = (x : ℂ) * Z.trace * b f g) →
    GlobalTheory.RealLift.HasForm P Q R S x := by
  intro P Q R S x b hb hinv
  let φ : Pol P Q R S →ₐ[ℂ] Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S := aeval (toTens P Q R S)
  let μ : Pol P Q R 0 ⊗[ℂ] Pol P Q 0 S →ₐ[ℂ] Pol P Q R S :=
    Algebra.TensorProduct.productMap (rename (jR P Q R S)) (rename (jS P Q R S))
  have hμ : ∀ f g, μ (f ⊗ₜ g) = rename (jR P Q R S) f * rename (jS P Q R S) g := fun f g =>
    Algebra.TensorProduct.productMap_apply_tmul _ _ _ _
  have hφR : ∀ f, φ (rename (jR P Q R S) f) = f ⊗ₜ 1 := by
    intro f
    have : φ.comp (rename (jR P Q R S)) = Algebra.TensorProduct.includeLeft := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · simp [φ, toTens, jR]
      · exact c.elim0
    simpa using congrArg (fun h => h f) this
  have hφS : ∀ g, φ (rename (jS P Q R S) g) = 1 ⊗ₜ g := by
    intro g
    have : φ.comp (rename (jS P Q R S)) = Algebra.TensorProduct.includeRight := by
      apply MvPolynomial.algHom_ext
      rintro ⟨a, c | c⟩
      · exact c.elim0
      · simp [φ, toTens, jS]
    simpa using congrArg (fun h => h g) this
  have hφ : ∀ f g, φ (rename (jR P Q R S) f * rename (jS P Q R S) g) = f ⊗ₜ g := by
    intro f g; rw [map_mul, hφR, hφS, Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have hμφ : μ.comp φ = AlgHom.id ℂ _ := by
    apply MvPolynomial.algHom_ext
    rintro ⟨a, c | c⟩
    · simp [φ, μ, toTens, jR]
    · simp [φ, μ, toTens, jS]
  let l : Pol P Q R S →ₗ[ℂ] ℂ := TensorProduct.lift b ∘ₗ φ.toLinearMap
  have hl : ∀ f g, l (rename (jR P Q R S) f * rename (jS P Q R S) g) = b f g := by
    intro f g; simp [l, hφ]
  refine ⟨l, ?_, ?_⟩
  · intro h0
    apply hb
    refine LinearMap.ext fun f => LinearMap.ext fun g => ?_
    have := congrArg (fun m => m (rename (jR P Q R S) f * rename (jS P Q R S) g)) h0
    simpa [hl] using this
  · intro Z F
    have key : ∀ t, l (fockAct1 P Q R S Z (μ t)) = (x : ℂ) * Z.trace * l (μ t) := by
      intro t
      induction t using TensorProduct.induction_on with
      | zero => simp
      | tmul f g => rw [hμ, fockAct1_rename_mul, map_add, hl, hl, hl, hinv]
      | add t₁ t₂ h₁ h₂ => simp only [map_add, h₁, h₂, mul_add]
    have hF : μ (φ F) = F := by simpa using congrArg (fun h => h F) hμφ
    simpa [hF] using key (φ F)

end GlobalTheory.FockSplit
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesThirdStatement
section
open NumberField Matrix Complex MeasureTheory IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct Classical ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option maxHeartbeats 1000000 in
theorem _root_.GlobalTheory.T.oscillator_model_values_third : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A) (κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)) (v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec), R.Char F → TieIn T R κ v₀ → ∀ (i : Fin D.R.m) (Tp : Type) (tup : Tp → T0) (O : OMDat T.toCore R i Tp tup), O.Pins (κ i) (v₀ i (sg0 D A)) (iotaW T i) (T.x₀ ((i : ℕ) + 1) O.s0) → ∀ (t : Tp) (k : O.Cl' t) (h : GA D (Vc D i)) (e : AE D) (P : Finset (Formalism.L2.DIV.Pl D.host.E)) (y : (AE D)ˣ), IsIdemSum e P → (∀ PP ∈ P, ((O.bad t : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal) → SuppAt e (Vc D i) h → IsDetAt e (Vc D i) h y → O.Lh t k = Bridge.hLat (Vc D i) (fin (Vc D i) h) → (∀ PP, PP ∈ R.Pg ∨ PP ∈ R.Q (tup t) → ((O.bad t : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) → inC O.c' (O.ep t k * (((O.La t k).mIdx (O.Nc t k) D.R.r : O.c'.F))⁻¹ * ((O.La t k).zCard (O.Nc t k) D.R.r : O.c'.F)) = (((Lift.chrTh (R.toLevCh.mu (tup t)) R.eta ((i : ℕ) + 1)).2 y : Circle) : ℂ)⁻¹ * (Real.sqrt (((((O.La t k).La ⊓ Formalism.L2.Pj.stdLat D.host.E (Vc D i).rank).toAddSubgroup.addSubgroupOf (O.La t k).La.toAddSubgroup).index : ℝ) ^ D.R.r) : ℂ) := by
  first | exact @GlobalTheory.ClassScalarValue.class_scalar_value | exact GlobalTheory.ClassScalarValue.class_scalar_value | (intros; apply GlobalTheory.ClassScalarValue.class_scalar_value <;> assumption)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PairOfC
section
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

noncomputable section
namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

def RegEl (G : HTGroup p) (y : G.Cˣ) : Prop :=
  (minpoly G.F (y : G.C)).natDegree = G.n ∧ (minpoly G.F (y : G.C)).Separable

def pairOf {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) : Pair G :=
  ⟨F.β, (r : G.Cˣ × ℚˣ).1, (r : G.Cˣ × ℚˣ).2, F.sym, r.2.1, h, F.trivAf, F.trivR⟩

end GlobalTheory.LKCx

namespace GlobalTheory.LKCx
variable {p : ℕ} [Fact p.Prime]

theorem pairOf_β {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).β = F.β := rfl

theorem pairOf_γ {G : HTGroup p} (F : Form G) (r : grp G F.β) (h : RegEl G (r : G.Cˣ × ℚˣ).1) :
    (pairOf F r h).γ = (r : G.Cˣ × ℚˣ).1 := rfl

open GlobalTheory.LKTrip.Example GlobalTheory.LKMid.Example in

example : ∃ (h : RegEl (ex 1 one_ne_zero) exPair.γ),
    pairOf (Form.ofPair exPair) ⟨(exPair.γ, exPair.c), exPair.sim, by show (0:ℚ) < 5; norm_num⟩ h = exPair :=
  ⟨exPair.reg, rfl⟩

end GlobalTheory.LKCx
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.DivisorProofs.PowMultiplicityDvdFixFirstBlock
section
open MvPolynomial GlobalTheory.ChowHt
attribute [local instance] MvPolynomial.gradedAlgebra

set_option autoImplicit false

namespace GlobalTheory.ChowSection

theorem totalDegree_of_isChowFormInt {k : Type} [Field k] {N e d : ℕ}
    {Q : Ideal (MvPolynomial (Fin N) k)} {g : MvPolynomial (Fin (e + 1) × Fin N) k}
    (h : IsChowFormInt Q e d g) : g.totalDegree = (e + 1) * d := by
  rw [((isMultiHomogeneous_iff_block.1 h.homog).isHomogeneous).totalDegree h.ne_zero]
  simp

end GlobalTheory.ChowSection
end

