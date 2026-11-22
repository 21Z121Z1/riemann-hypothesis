import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.RingSpecNormalisedCharacterEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0005
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.Bundle0007
import Formalism.LocalToGlobal.IndefiniteReal.Bundle0023
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.MemHatIffOfSelfDual
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.LatAtLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValuedLtOfMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0132
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsMoveRight
import Formalism.LocalToGlobal.Columns.Bundle0016
import Formalism.LocalToGlobal.Columns.RecLevelCls
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LambdaCharSymMulInvEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0174
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0245
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0433
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0330
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LintegralCompactLe
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0138
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.Bundle0125
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Bundle0238
import Development.AbelianVarietyTheory.Counterexamples.HeightSurvey.Bundle0003

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.StandardFrameConjugateClose
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev Formalism.IndefR.RecTie Formalism.L2.Rows GlobalTheory.Mem GlobalTheory.Mem.R3 ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open GlobalTheory.StdFrames GlobalTheory.AdIsom GlobalTheory.IdemSupport

namespace GlobalTheory.ConjLt
variable {D : D7}

theorem lt_one_le_exp {x : WithZero (Multiplicative ℤ)} (h : x < 1) : x ≤ WithZero.exp (-1) := by
  rcases eq_or_ne x 0 with rfl | hx
  · exact zero_le'
  · obtain ⟨n, rfl⟩ := WithZero.ne_zero_iff_exists.1 hx
    have : (n : WithZero (Multiplicative ℤ)) = WithZero.exp (Multiplicative.toAdd n) := rfl
    rw [this, ← WithZero.exp_zero, WithZero.exp_lt_exp] at h
    rw [this, WithZero.exp_le_exp]
    omega

theorem cpt_sg_lt_one (Q : Pl D.host.E) (z : EAf D) (h : Valued.v (cpt Q z) < 1) :
    Valued.v (cpt (cP Q) (sg D z)) < 1 := by
  obtain ⟨π, hπ⟩ := Q.intValuation_exists_uniformizer
  set p : D.host.E := (π : D.host.E) with hp
  have hvp : Valued.v (cpt Q (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p)) = WithZero.exp (-1) := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap, hp, ← hπ]
    exact Q.valuation_of_algebraMap π
  have hp0 : p ≠ 0 := by
    rintro h0
    rw [h0, map_zero, map_zero, map_zero] at hvp
    exact WithZero.exp_ne_zero hvp.symm
  set a := z * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p⁻¹ with ha
  have hza : z = a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D p := by
    rw [ha, mul_assoc, ← map_mul, inv_mul_cancel₀ hp0, map_one, mul_one]
  have hva : Valued.v (cpt Q a) ≤ 1 := by
    have e1 : Valued.v (cpt Q a) * WithZero.exp (-1) = Valued.v (cpt Q z) := by
      rw [← hvp, ← Valuation.map_mul, ← map_mul, ← hza]
    have e2 := lt_one_le_exp h
    rw [← e1] at e2
    by_contra hc
    push_neg at hc
    have : WithZero.exp (-1) < Valued.v (cpt Q a) * WithZero.exp (-1) := by
      calc WithZero.exp (-1) = 1 * WithZero.exp (-1) := (one_mul _).symm
        _ < _ := mul_lt_mul_of_pos_right hc (WithZero.exp_pos)
    exact absurd e2 (not_le.2 this)
  have h1 := (cpt_cjA_le_iff Q a).2 hva
  have hs : sg D z = GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.cjA D a * GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p) := by
    rw [hza, map_mul]; rfl
  have h2 : Valued.v (cpt (cP Q) (GlobalTheory.IndefiniteRowSideFullHecke.FlatSpaceComponents.inc D (star p))) < 1 := by
    rw [cpt_inc, Formalism.UG.P.levelaf_valued_algebraMap]
    have e : star p = ((cO D π : 𝓞 D.host.E) : D.host.E) := rfl
    rw [e, (cP Q).valuation_lt_one_iff_mem, mem_cP, cO_cO, ← Q.intValuation_lt_one_iff_mem, hπ]
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]; norm_num
  rw [hs, map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' h1) h2

theorem conj_sub_one {A : Type} [CommRing A] (σ : A →+* A) {n : ℕ} (β x : GL (Fin n) A)
    (R U' : Matrix (Fin n) (Fin n) A) (hX : Formalism.UG.cT σ x.val * R * x.val = R)
    (hU : U' * (Formalism.UG.cT σ β.val * R * β.val) = 1) :
    (β⁻¹ * x * β).val - 1 = U' * (Formalism.UG.cT σ (β⁻¹ * x⁻¹ * β).val - 1) * (Formalism.UG.cT σ β.val * R * β.val) := by
  set G := Formalism.UG.cT σ β.val * R * β.val with hG
  set Y := (β⁻¹ * x * β).val with hYdef
  set Yi := (β⁻¹ * x⁻¹ * β).val with hYidef
  have hYYi : Y * Yi = 1 := by
    rw [hYdef, hYidef, ← Units.val_mul]
    rw [show β⁻¹ * x * β * (β⁻¹ * x⁻¹ * β) = 1 by group, Units.val_one]
  have hY : Y = (β⁻¹).val * x.val * β.val := by rw [hYdef, Units.val_mul, Units.val_mul]
  have c1 : ∀ Z : Matrix (Fin n) (Fin n) A, Formalism.UG.cT σ (β⁻¹).val * (Formalism.UG.cT σ β.val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, ← cT_mul', Units.mul_inv, cT_one', Matrix.one_mul]
  have c2 : ∀ Z : Matrix (Fin n) (Fin n) A, β.val * ((β⁻¹).val * Z) = Z := by
    intro Z
    rw [← Matrix.mul_assoc, Units.mul_inv, Matrix.one_mul]
  have hUY : Formalism.UG.cT σ Y * G * Y = G := by
    rw [hY, hG, cT_mul', cT_mul']
    simp only [Matrix.mul_assoc, c1, c2]
    rw [show Formalism.UG.cT σ x.val * (R * (x.val * β.val)) = (Formalism.UG.cT σ x.val * R * x.val) * β.val by
        simp only [Matrix.mul_assoc], hX]
  have hGY : G * Y = Formalism.UG.cT σ Yi * G := by
    have := congrArg (fun Z => Formalism.UG.cT σ Yi * Z) hUY
    rw [← this, ← Matrix.mul_assoc, ← Matrix.mul_assoc, ← cT_mul', hYYi, cT_one', Matrix.one_mul]
  have e1 : Y = U' * (G * Y) := by rw [← Matrix.mul_assoc, hU, Matrix.one_mul]
  calc Y - 1 = U' * (G * Y) - U' * G := by rw [← e1, hU]
    _ = U' * (Formalism.UG.cT σ Yi * G) - U' * G := by rw [hGY]
    _ = U' * (Formalism.UG.cT σ Yi - 1) * G := by
      rw [Matrix.mul_sub, Matrix.mul_one, Matrix.sub_mul, Matrix.mul_assoc]

theorem frame_mat_sub_one_lt : ∀ (D : D7) (V : HSp D) (β : GL (Fin V.rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)) (N : ℕ), IsSDFrame V β Λ N → ∀ (g : GA D V) (Q : Formalism.L2.DIV.Pl D.host.E), (∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt Q ((β⁻¹ * (finE V g)⁻¹ * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1) → ∀ a b : Fin V.rank, Valued.v (GlobalTheory.StdFrames.cpt (GlobalTheory.IdemSupport.cP Q) ((β⁻¹ * finE V g * β).val a b - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) a b)) < 1 := by
  intro D V β Λ N hSD g Q h a b
  obtain ⟨hGi, U', hU'i, hU'⟩ := unimod_of_isSD hSD
  have hX : Formalism.UG.cT (sg D) (finE V g).val * GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram * (finE V g).val =
      GlobalTheory.IndefiniteRowSideFullHecke.ChainMatrices.ratM V.gram := GlobalTheory.LevSplit.finE_mem_UA V g
  have hYsub := conj_sub_one (sg D) β (finE V g) _ U' hX hU'
  have hM : ∀ i j, Valued.v (cpt (cP Q) ((Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j)) < 1 := by
    intro i j
    have e : (Formalism.UG.cT (sg D) (β⁻¹ * (finE V g)⁻¹ * β).val - 1) i j =
        sg D ((β⁻¹ * (finE V g)⁻¹ * β).val j i - (1 : Matrix (Fin V.rank) (Fin V.rank) (EAf D)) j i) := by
      simp only [Formalism.UG.cT, Matrix.sub_apply, Matrix.transpose_apply, Matrix.map_apply, map_sub, Matrix.one_apply]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (Ne.symm hij), map_zero]
    rw [e]
    exact cpt_sg_lt_one Q _ (h j i)
  have hint : ∀ x ∈ GlobalTheory.StdFrames.OA D, Valued.v (cpt (cP Q) x) ≤ 1 := fun x hx => (mem_OA x).1 hx (cP Q)
  rw [← Matrix.sub_apply, hYsub, Matrix.mul_apply, map_sum]
  refine Valuation.map_sum_lt' _ zero_lt_one fun j _ => ?_
  rw [map_mul, Valuation.map_mul, Matrix.mul_apply, map_sum]
  refine lt_of_le_of_lt (mul_le_of_le_one_right' (hint _ (hGi j b))) ?_
  refine Valuation.map_sum_lt' _ zero_lt_one fun i _ => ?_
  rw [map_mul, Valuation.map_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_left' (hint _ (hU'i a i))) (hM i j)

end GlobalTheory.ConjLt
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SymmetricLevelBoundLe
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 Matrix
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.Mem.LastGrp

open GlobalTheory.SymLevelInv LocE Loc

theorem posSym_eq_symIdx (k rS x : ℕ) : posSym k rS x = symIdx k rS x := by
  unfold posSym symIdx
  split_ifs <;> omega

theorem symmetric_level_bound_le (k rS s : ℕ) : bd5 k rS s ≤ s := by
  unfold bd5
  split_ifs <;> omega

variable {E : Type} [Field E] [NumberField E] [StarRing E] {P : HeightOneSpectrum (𝓞 E)} {q : ℕ}

theorem inJSym_of_mat (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n : ℕ} (hr : r = rSym k rS) (ht : 0 < t) (hn : r ≤ n)
    {g : Sp E (n + 0) ≃ₗ[E] Sp E (n + 0)} (hg : g ∈ JGsym P q k rS r t n 0) {κ : Type} [Field κ]
    (e : (𝓞 E ⧸ P.asIdeal) →+* κ) (M : Matrix (Fin n) (Fin n) κ) (hM : ∀ i j : Fin n, M i j = e (redP P (mat g i j))) :
    InJSym k rS t false M := by
  subst hr
  have hr' : k + rS < rSym k rS := by
    unfold rSym
    omega
  refine ⟨fun x y h => ?_, fun x hx => ?_, fun x y hx hy => ?_, fun h => by simp at h⟩
  · have hxy : x.1 ≠ y.1 := fun h' => by rw [h'] at h; omega
    by_cases hy : y.1 < rSym k rS
    · have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
        refine (symmetric_level_bound_le _ _ _).trans ?_
        rw [lvSym_of_lt hy, posSym_eq_symIdx] at h
        by_cases hx : x.1 < rSym k rS
        · rw [lvSym_of_lt hx, posSym_eq_symIdx] at h
          exact h.le
        · have h1 := symIdx_lt hr'.le hy
          have h2 := symIdx_cases k rS x.1
          omega
      rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hy key, if_neg hxy, map_zero]
    · have hx : ¬ x.1 < rSym k rS := by
        intro hx
        have h1 := lvSym_of_ge (t := t) hy
        rw [lvSym_of_lt hx] at h
        have h2 := posSym_lt hx
        omega
      unfold lvSym at h
      rw [if_neg hy, if_neg hx] at h
      have h1 : (y.1 - rSym k rS) / t + 1 ≤ (x.1 - rSym k rS) / t := by omega
      have h2 := Nat.lt_mul_div_succ (y.1 - rSym k rS) ht
      have h3 := Nat.div_mul_le_self (x.1 - rSym k rS) t
      have h4 := Nat.mul_le_mul_right t h1
      rw [mul_comm] at h2
      rw [hM, mat_blk hq hP hr' hg ((y.1 - rSym k rS) / t + 1) x.1 y.1 x.2 (by omega) (by omega), map_zero]
  · rw [hM, mat_col hq hP hr' hn hg x.1 x.1 x.2 hx (symmetric_level_bound_le _ _ _), if_pos rfl, map_one]
  · have hyr : y.1 < rSym k rS := by omega
    have key : bd5 k rS (symIdx k rS y.1) ≤ symIdx k rS x.1 := by
      rw [hy]
      unfold bd5 symIdx
      split_ifs <;> omega
    rw [hM, mat_col hq hP hr' hn hg x.1 y.1 x.2 hyr key, if_neg (by omega), map_zero]

theorem inJSym_of_prX (hq : q ≠ 0) (hP : (q : 𝓞 E) ∈ P.asIdeal) {k rS r t n c : ℕ} (hc : c = 0) (hr : r = rSym k rS) (ht : 0 < t)
    (hn : r ≤ n) {ρ : Sp E (n + c) ≃ₗ[E] Sp E (n + c)} (hρ : ρ ∈ JGsym P q k rS r t n c) {g : Sp E n ≃ₗ[E] Sp E n}
    (hx : ∀ x, ρ (Loc.inX E n c x) = Loc.inX E n c (g x)) {κ : Type} [Field κ] (e : (𝓞 E ⧸ P.asIdeal) →+* κ)
    (M : Matrix (Fin n) (Fin n) (𝓞 E ⧸ P.asIdeal)) (hM : ∀ x ∈ stdAt E n P, redV P (g x) = M.mulVec (redV P x)) :
    InJSym k rS t false (M.map e) := by
  subst hc
  refine inJSym_of_mat hq hP hr ht hn hρ e _ fun i j => ?_
  have h6 := congrFun (hM _ (TopStep.single_mem_stdAt j)) i
  rw [TopStep.redV_single, Matrix.mulVec_single_one] at h6
  have h7 : mat ρ i.1 j.1 = g (Pi.single j 1) i := by
    have h8 : eN E (n + 0) j.1 = Loc.inX E n 0 (Pi.single j 1) := by
      funext l
      rw [CongLevel.inX_apply, dif_pos (show l.1 < n from l.2)]
      unfold Loc.eN
      simp [Pi.single_apply, Fin.ext_iff]
    unfold mat atN
    rw [dif_pos (show i.1 < n + 0 from i.2), h8, hx, CongLevel.inX_apply, dif_pos i.2]
  rw [Matrix.map_apply, h7]
  exact congrArg e h6.symm

end GlobalTheory.Mem.LastGrp

theorem GlobalTheory.Mem.LastGrp.levG_le_JSymG : ∀ {X : Fields} {Pr : Primes X} {R : Ranks} (Ch : Chars X Pr R.m) (sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)) {S : Set ℕ} (mu : Tup X.F X.E X.K S) (cst : LocCst X (rowSG Pr sel mu)) (L : ChIdx X Pr R (QE sel (mu : Chr X.F X.E X.K))) (G : ChGlob X R.m) (m2 : ℕ), X.Ok → Pr.Ok → IsSel X sel → L.Ok Ch sel mu cst G m2 → cst.sharp = true → ∀ (j : ℕ), j + 1 = R.m → ∀ (b : L.β j) (w : {w // w ∈ Pr.vGs}) (κ : Type) [Field κ] (e : (𝓞 X.E ⧸ w.1.asIdeal) ≃+* κ) (M : GL (Fin (R.N j)) (𝓞 X.E ⧸ w.1.asIdeal)), M ∈ (L.levG j b w).H → Matrix.GeneralLinearGroup.map e.toRingHom M ∈ JSymG κ (R.N j) R.k (rSD R) R.t false := by
  intro X Pr R Ch sel S mu cst L G m2 hX hPr hSel hL hs j hj b w κ _ e M hM
  letI : StarRing X.E := X.starE
  have hm := hL.hm
  obtain rfl : j = m2 + 1 := by omega
  have hc : cOf R (m2 + 1) = 0 := by
    unfold cOf
    omega
  have hq : qOf w.1 ≠ 0 := fun h => TopStep.qOf_ne_zero (P := w.1) (by rw [h]; simp)
  have hP : ((qOf w.1 : ℕ) : 𝓞 X.E) ∈ w.1.asIdeal := Ideal.absNorm_mem _
  have hr : R.r = rSym R.k (rSD R) := by
    obtain ⟨a, ha⟩ := R.m_even
    unfold Ranks.r rSym rSD
    omega
  have ht : 0 < R.t := by
    have := R.three_m_lt_t
    omega
  have hn : R.r ≤ R.N (m2 + 1) := by
    unfold Ranks.r Ranks.N
    rw [mul_add, mul_one]
    omega
  have key : ∀ A : GL (Fin (R.N (m2 + 1))) (𝓞 X.E ⧸ w.1.asIdeal), A ∈ (L.levG (m2 + 1) b w).H →
      InJSym R.k (rSD R) R.t false ((A.1).map e.toRingHom) := by
    intro A hA
    obtain ⟨g, hg, hred⟩ := (hL.grpG _ b w A).1 hA
    unfold prCat at hg
    rw [hL.last_h] at hg
    obtain ⟨ρ, hρ, hx⟩ := hg
    have hJ : ρ ∈ Jat (Pr := Pr) cst.sharp (m2 + 1) w.1 := by simpa [Loc.Cbe] using hρ.2
    unfold Jat at hJ
    rw [if_pos w.2, if_pos hs] at hJ
    exact inJSym_of_prX hq hP hc hr ht hn hJ hx e.toRingHom A.1 hred
  refine ⟨key M hM, ?_⟩
  rw [← map_inv]
  exact key _ (inv_mem hM)
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ThetaLiftDefiniteSmoothModerateGrowthAnnihilated
section
open NumberField IsDedekindDomain MeasureTheory Matrix Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT GlobalTheory.HolDict
open scoped TensorProduct InnerProductSpace ContDiff ComplexOrder
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DefLift

namespace GlobalTheory.DefLiftSmooth

theorem lift_growth (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle)
    (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (hW : IsWeilDatumO ψ S T χS χT om)
    (θ : InfFam D) (hθ : IsInfFam θ) (hS : ∀ τ, (gramAt D S τ).PosDef)
    (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X]
    (F : GA D S → X) (hF : Continuous F) (hFi : ∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h)
    (ν : Measure (GA D S)) (𝓕 : Set (GA D S)) (hν : ν.IsHaarMeasure) (h𝓕 : IsFundamentalDomain (GQ S) 𝓕 ν) :
    ∃ N : ℕ, ∀ L : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ x : GA D T,
      ∃ c : ℝ, ∀ g ∈ GinfC T, ‖lift om ν 𝓕 (fun h => L (F h)) (x * g)‖ ≤ c * normInf θ T g ^ N := by
  obtain ⟨N, hN⟩ := GlobalTheory.ThetaGrowth.thetaKO_growth ψ S T χS χT om hW θ hθ
  obtain ⟨C, hC, hcov⟩ := GlobalTheory.definite_unitary_cocompact S hS
  have hfin : ν 𝓕 < ⊤ := lt_top_iff_ne_top.2 (GlobalTheory.Mem.QuotVol.quot_volume_ne_zero_ne_top D S ν 𝓕 ⟨hν, h𝓕⟩).2
  refine ⟨N, fun L hL x => ?_⟩
  let b := Module.finBasis ℂ X
  choose c hc using fun j => hN (L (b j)) (hL _) x C hC
  have hco : ∀ j, ∃ M : ℝ, ∀ h ∈ C, ‖b.repr (F h) j‖ ≤ M := fun j =>
    hC.exists_bound_of_continuousOn
      (((b.coord j).continuous_of_finiteDimensional.comp hF).continuousOn)
  choose M hM using hco
  refine ⟨(∑ j, M j * c j) * ν.real 𝓕, fun g hg => ?_⟩
  have key : ∀ h, ‖thetaKO om h (x * g) (L (F h))‖ ≤ (∑ j, M j * c j) * normInf θ T g ^ N := by
    intro h
    obtain ⟨γ, hγ, k, hk, rfl⟩ := hcov h
    have hinv := (GlobalTheory.thetaKO_continuous_and_rat_invariant ψ S T χS χT om hW (L (F k)) (hL _)).2 γ hγ 1
      (one_mem _) k (x * g)
    rw [one_mul] at hinv
    rw [hFi γ hγ, hinv]
    have e : thetaKO om k (x * g) (L (F k)) = ∑ j, b.repr (F k) j * thetaKO om k (x * g) (L (b j)) := by
      conv_lhs => rw [← b.sum_repr (F k)]
      simp only [thetaKO, map_sum, map_smul, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
    rw [e, Finset.sum_mul]
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [norm_mul, mul_assoc]
    exact mul_le_mul (hM j k hk) (hc j k hk g hg) (norm_nonneg _) ((norm_nonneg _).trans (hM j k hk))
  calc _ ≤ (∑ j, M j * c j) * normInf θ T g ^ N * ν.real 𝓕 :=
        norm_setIntegral_le_of_norm_le_const hfin fun h _ => key h
    _ = _ := by ring

theorem lift_smooth_growth_killed : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (S T : HSp D) (χS χT : (AE D)ˣ →* Circle) (om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)), IsWeilDatumO ψ S T χS χT om → ∀ θ : InfFam D, IsInfFam θ → (∀ τ, (gramAt D S τ).PosDef) → ∀ (X : Type) [NormedAddCommGroup X] [NormedSpace ℂ X] [FiniteDimensional ℂ X] (L : X →ₗ[ℂ] (WO S T → ℂ)), (∀ x, IsThetaFunO ψ S T (L x)) → ∀ F : GA D S → X, Continuous F → (∀ γ ∈ GQ S, ∀ h, F (γ * h) = F h) → ∀ (ν : Measure (GA D S)) (𝓕 : Set (GA D S)), ν.IsHaarMeasure → IsFundamentalDomain (GQ S) 𝓕 ν → GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsSmoothFn T θ (lift om ν 𝓕 fun h => L (F h)) ∧ GlobalTheory.IndefiniteRowSideFullHecke.HolomorphicParabolicSmoothFunctions.IsUnifModGrowth T θ (lift om ν 𝓕 fun h => L (F h)) ∧ ∀ τ (Z : Mt T.rank), (∀ x h, RderC θ T τ Z (fun g => thetaKO om h g (L x)) = 0) → RderC θ T τ Z (lift om ν 𝓕 fun h => L (F h)) = 0 := by
  intro D ψ S T χS χT om hW θ hθ hS X _ _ _ L hL F hF hFi ν 𝓕 hν h𝓕
  have hder := fun (L : X →ₗ[ℂ] (WO S T → ℂ)) (hL : ∀ x, IsThetaFunO ψ S T (L x)) =>
    GlobalTheory.T.definiteThetaLift_continuous_invariant_hasDerivAt D ψ S T χS χT om hW θ hθ hS X L hL F hF hFi ν 𝓕 hν h𝓕
  refine ⟨?_, ?_, ?_⟩
  · refine GlobalTheory.Mem.DerClosed.mem_smFun_of_closed D θ hθ T
      {φ | ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧ φ = lift om ν 𝓕 fun h => L' (F h)}
      ?_ ?_ _ ⟨L, hL, rfl⟩
    · rintro φ ⟨L', hL', rfl⟩
      exact (hder L' hL').1.1
    · rintro φ ⟨L', hL', rfl⟩ τ Y hY
      obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 τ Y hY
      exact ⟨_, ⟨L'', h1, rfl⟩, h3⟩
  · obtain ⟨N, hN⟩ := lift_growth D ψ S T χS χT om hW θ hθ hS X F hF hFi ν 𝓕 hν h𝓕
    refine ⟨N, fun l hl x => ?_⟩
    have hw : ∃ L' : X →ₗ[ℂ] (WO S T → ℂ), (∀ x, IsThetaFunO ψ S T (L' x)) ∧
        List.foldr (fun p f => Rder θ T p.1 p.2 f) (lift om ν 𝓕 fun h => L (F h)) l
          = lift om ν 𝓕 fun h => L' (F h) := by
      induction l with
      | nil => exact ⟨L, hL, rfl⟩
      | cons p l ih =>
        obtain ⟨L', hL', e⟩ := ih fun q hq => hl q (List.mem_cons_of_mem _ hq)
        obtain ⟨L'', h1, -, h3⟩ := (hder L' hL').2 p.1 p.2 (hl p List.mem_cons_self)
        refine ⟨L'', h1, ?_⟩
        rw [List.foldr_cons, e]
        exact funext fun g => (h3 g).deriv
    obtain ⟨L', hL', e⟩ := hw
    rw [e]
    exact hN L' hL' x
  · intro τ Z hZ
    obtain ⟨hY₁, hY₂⟩ := GlobalTheory.SmoothAutCheck.parts_mem T τ Z
    obtain ⟨L₁, -, a₁, b₁⟩ := (hder L hL).2 τ _ hY₁
    obtain ⟨L₂, -, a₂, b₂⟩ := (hder L hL).2 τ _ hY₂
    funext g
    have hp : ∀ h, thetaKO om h g (L₁ (F h)) = -Complex.I * thetaKO om h g (L₂ (F h)) := by
      intro h
      have := congrFun (hZ (F h) h) g
      simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at this
      rw [(a₁ (F h) h g).deriv, (a₂ (F h) h g).deriv] at this
      linear_combination this
    simp only [RderC, Rder, Pi.add_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
    rw [(b₁ g).deriv, (b₂ g).deriv]
    simp only [lift, hp, integral_const_mul]
    ring

end GlobalTheory.DefLiftSmooth
end

-- bundled from Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ValSubLtOfHasRes
section
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Mem.Col2.PtStab

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

theorem hasRes_of_sub {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (hab : Valued.v (a - b) < 1) : HasRes P b c := by
  obtain ⟨r, hr, hv⟩ := h
  refine ⟨r, hr, ?_⟩
  have e : b - algebraMap E _ (algebraMap (𝓞 E) E r) = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (a - b) := by ring
  rw [e]
  exact Valuation.map_sub_lt _ hv hab

theorem val_sub_lt_of_hasRes {P : HeightOneSpectrum (𝓞 E)} {a b : P.adicCompletion E} {c : 𝓞 E ⧸ P.asIdeal}
    (h : HasRes P a c) (h' : HasRes P b c) : Valued.v (a - b) < 1 := by
  obtain ⟨r, hr, hv⟩ := h
  obtain ⟨r', hr', hv'⟩ := h'
  have hmem : r - r' ∈ P.asIdeal := Ideal.Quotient.eq.1 (hr.trans hr'.symm)
  have e : a - b = (a - algebraMap E _ (algebraMap (𝓞 E) E r)) - (b - algebraMap E _ (algebraMap (𝓞 E) E r')) +
      algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E (r - r')) := by
    simp only [map_sub]
    ring
  rw [e]
  refine Valuation.map_add_lt _ (Valuation.map_sub_lt _ hv hv') ?_
  rw [valued_algebraMap]
  exact (HeightOneSpectrum.valuation_lt_one_iff_mem _ _).2 hmem

theorem val_sub_lt_of_hatL {n : ℕ} (a b : Matrix (Fin n) (Fin n) (AfE F E)) (P : HeightOneSpectrum (𝓞 E)) (i : Fin n)
    {N : Submodule (𝓞 E) (Fin n → E)}
    (h : ∀ y ∈ N, Valued.v (adAt F P ((a *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i -
      (b *ᵥ fun j => Formalism.UG.inclE (F := F) (FiniteAdeleRing (𝓞 F) F) (y j)) i)) < 1)
    {z : Fin n → AfE F E} (hz : z ∈ Formalism.L2.Herm.hatL (F := F) N) :
    Valued.v (adAt F P ((a *ᵥ z) i - (b *ᵥ z) i)) < 1 := by
  induction hz using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨v, hv, rfl⟩ := hx
    exact h v hv
  | zero => simp
  | add x y _ _ hx hy =>
    have e : (a *ᵥ (x + y)) i - (b *ᵥ (x + y)) i = ((a *ᵥ x) i - (b *ᵥ x) i) + ((a *ᵥ y) i - (b *ᵥ y) i) := by
      simp only [Matrix.mulVec_add, Pi.add_apply]
      ring
    rw [e, map_add (adAt F P)]
    exact Valuation.map_add_lt _ hx hy
  | smul c x _ hx =>
    have e0 : c • x = (c : AfE F E) • x := rfl
    have e : (a *ᵥ (c • x)) i - (b *ᵥ (c • x)) i = (c : AfE F E) * ((a *ᵥ x) i - (b *ᵥ x) i) := by
      rw [e0, Matrix.mulVec_smul, Matrix.mulVec_smul, Pi.smul_apply, Pi.smul_apply, smul_eq_mul, smul_eq_mul]
      ring
    rw [e, map_mul, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' ((mem_rInt_iff F E _).1 c.2 P)) hx

variable [StarRing E] {hc : Formalism.BasicNotions.CMData F E} {n : ℕ} {ST SG Q : Finset (HeightOneSpectrum (𝓞 E))}

theorem pullV_mul_stab (g g' h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x =
      ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
        ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  unfold GlobalTheory.Mem.Col2.pullV
  simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]

theorem pullV_eq_of_mul (g h : GL (Fin n) (AfE F E)) (x : Sp E n) :
    GlobalTheory.Mem.Col2.pullV h x = ((g⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
                 ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x) := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]

theorem val_sub_pullV_lt {g g' h : GL (Fin n) (AfE F E)} {p q : DecoF E n ST SG Q}
    (hg : IsPtOf hc g p) (hh : IsPtOf hc h q) {P : HeightOneSpectrum (𝓞 E)} (i : Fin n)
    (hP : ∀ y ∈ p.deco.1.N, Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV g y i - GlobalTheory.Mem.Col2.pullV g' y i)) < 1)
    {x : Sp E n} (hx : x ∈ q.deco.1.N) :
    Valued.v (adAt F P (GlobalTheory.Mem.Col2.pullV h x i - GlobalTheory.Mem.Col2.pullV (h * (g⁻¹ * g')) x i)) < 1 := by
  have hu : GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) (stdLat E n) :=
    (hh.lat _).1 (Submodule.subset_span ⟨x, hx, rfl⟩)
  have hz : (g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ GlobalTheory.Mem.Col2.pullV h x ∈ Formalism.L2.Herm.hatL (F := F) p.deco.1.N := by
    refine (hg.lat _).2 ?_
    rwa [← pullV_eq_of_mul]
  have := val_sub_lt_of_hatL _ _ P i (fun y hy => hP y hy) hz
  rwa [← pullV_eq_of_mul, ← pullV_mul_stab] at this

theorem isPtOf_mul_stab : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] [StarRing E] (hc : Formalism.BasicNotions.CMData F E) (n : ℕ) (ST SG Q : Finset (HeightOneSpectrum (𝓞 E))), ∀ (g g' h : GL (Fin n) (AfE F E)) (p q : DecoF E n ST SG Q), IsPtOf hc g p → IsPtOf hc g' p → IsPtOf hc h q → IsPtOf hc (h * (g⁻¹ * g')) q := by
  intro F E _ _ _ _ _ _ hc n ST SG Q g g' h p q hg hg' hh
  refine ⟨mul_mem hh.uni (mul_mem (inv_mem hg.uni) hg'.uni), fun x => ?_, fun P x hx i hi => ?_, fun w x hx i => ?_,
    fun P i j => ?_⟩
  · have e : (((h * (g⁻¹ * g'))⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x =
        ((g'⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
          ((g : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ
            (((h⁻¹ : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) *ᵥ x)) := by
      simp only [Matrix.mulVec_mulVec, ← Units.val_mul, _root_.mul_inv_rev, inv_inv, mul_assoc]
    rw [e, hh.lat x, ← hg'.lat, hg.lat, Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one,
      Matrix.one_mulVec]
  · refine hasRes_of_sub (hh.f P x hx i hi) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.f P y hy i hi) (hg'.f P y hy i hi)
  · refine hasRes_of_sub (hh.be w x hx i) ?_
    rw [← map_sub]
    refine val_sub_pullV_lt hg hh i (fun y hy => ?_) hx
    rw [map_sub]
    exact val_sub_lt_of_hasRes (hg.be w y hy i) (hg'.be w y hy i)
  · have hgg : (g : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) =
        (g' : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) := by
      ext a b
      simp only [Matrix.map_apply]
      rw [hg.fr, hg'.fr]
    have hs : (((g⁻¹ * g' : GL (Fin n) (AfE F E))) : Matrix (Fin n) (Fin n) (AfE F E)).map (adAt F P.1) = 1 := by
      rw [Units.val_mul, Matrix.map_mul, ← hgg, ← Matrix.map_mul, ← Units.val_mul, inv_mul_cancel, Units.val_one,
        Matrix.map_one _ (map_zero _) (map_one _)]
    have e : adAt F P.1 (((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E)) i j) =
        ((((h * (g⁻¹ * g') : GL (Fin n) (AfE F E)) : Matrix (Fin n) (Fin n) (AfE F E))).map (adAt F P.1)) i j := rfl
    rw [e, Units.val_mul, Matrix.map_mul, hs, mul_one, Matrix.map_apply]
    exact hh.fr P i j

end GlobalTheory.Mem.Col2.PtStab

end
end

