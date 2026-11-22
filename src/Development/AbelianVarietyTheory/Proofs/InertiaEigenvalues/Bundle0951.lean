import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.Bundle0021
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0042
import Development.AbelianVarietyTheory.Definitions.ThetaValues.ExistsRootNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMapOfOfExtends
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.Bundle0006
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0249
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0936
import Formalism.LocalToGlobal.IndefiniteReal.FinitePlaces.FinPartDetAtInvInt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0122
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsDecompChainSpaceDefiniteAddNormalFrame
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0945
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0943
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.StrongMultiplicityOne
import Development.AbelianVarietyTheory.Definitions.Divisors.Bundle0025
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0958
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Bundle0835
import Formalism.SharpRestriction.LevelLetterCocycles.EmbeddingTypeJumps
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsUniqueHcharOfFiniteOrder
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0005
import Formalism.SharpRestriction.LevelLetterCocycles.JointConditionsZpowers.CommutingEndomorphismCondition
import Formalism.SharpRestriction.LevelLetterCocycles.Bundle0007
import Formalism.GaloisCohomology.LocalTateDualityK
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.RationalDualityOfAllCoefficients
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0946
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0511
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0858
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0306
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0708
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0676
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0769
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0318
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0644
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0667
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0547
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0641
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0272
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.Bundle0295
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.Bundle0064

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.OneAddSumEqProd
section
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice IsDedekindDomain NumberField Matrix Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ConjTwist GlobalTheory.GalTw ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Classical

namespace GlobalTheory.FlatConst

theorem one_add_sum_eq_prod {R ι : Type} [CommRing R] [DecidableEq ι] (s : Finset ι) (f a : ι → R)
    (h : ∀ i ∈ s, ∀ j ∈ s, i ≠ j → f i * f j = 0) :
    1 + ∑ i ∈ s, f i * (a i - 1) = ∏ i ∈ s, (1 + f i * (a i - 1)) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj,
      ← ih fun k hk l hl hkl => h k (Finset.mem_insert_of_mem hk) l (Finset.mem_insert_of_mem hl) hkl]
    have h0 : f j * (a j - 1) * ∑ k ∈ s, f k * (a k - 1) = 0 := by
      rw [Finset.mul_sum]
      refine Finset.sum_eq_zero fun k hk => ?_
      have hne : j ≠ k := fun e => hj (e ▸ hk)
      have := h j (Finset.mem_insert_self j s) k (Finset.mem_insert_of_mem hk) hne
      calc f j * (a j - 1) * (f k * (a k - 1)) = (f j * f k) * ((a j - 1) * (a k - 1)) := by ring
        _ = 0 := by rw [this, zero_mul]
    linear_combination (-1 : R) * h0

theorem chr_inv_val {D : D7} (c : (AE D)ˣ →* Circle) (x : (AE D)ˣ) : ((c x⁻¹ : Circle) : ℂ) = ((c x : Circle) : ℂ)⁻¹ := by
  rw [map_inv, Circle.coe_inv]

theorem chrW_val {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (i : Fin D.R.m) (t' : T0) (x : (AE D)ˣ) :
    (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ) =
      ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.xi t' x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹ := by
  unfold Lift.chrTh LevCh.mu Lift.tup
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, Circle.coe_mul, Circle.coe_inv]

end GlobalTheory.FlatConst

open GlobalTheory.FlatConst in

theorem GlobalTheory.FlatConst.flat_const : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : FamIn D.what₂.LL G Pl0 T0 D.R.m) (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (R : RealDat D A T.Q.c.F) (F : Face D A), GlobalTheory.Hk3.Core R F → ∀ (i : Fin D.R.m) (t : T0) (es : Pl D.host.E → AE D) (ϖ : Pl D.host.E → 𝓞 D.host.E) (n : ℕ) (x : (AE D)ˣ), (∀ PP ∈ R.Q t, Formalism.L2.NTheta.IsIdemAt (es PP) PP) → (∑ PP ∈ R.Q t, es PP) * cA D (∑ PP ∈ R.Q t, es PP) = 0 → (∀ PP ∈ R.Q t, ϖ PP ∈ PP.asIdeal ∧ ϖ PP ∉ PP.asIdeal ^ 2) → (x : AE D) = 1 + ∑ PP ∈ R.Q t, cA D (es PP) * (incA D (star (ϖ PP : D.host.E)) ^ n - 1) → ∃ b : ℂ, (∀ τ : ℂ ≃+* ℂ, FixBase T R i τ → τ (b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) = b * ∏ PP ∈ R.Q t, (((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ)⁻¹) ^ n) ∧ (∀ t' : T0, (((Lift.chrTh (R.toLevCh.mu t') R.eta ((i : ℕ) + 1)).2 x : Circle) : ℂ)⁻¹ = b * ((R.xi t' x⁻¹ : Circle) : ℂ)) ∧ (∀ (t' : T0) (S : Finset (Pl D.host.E)), S ⊆ R.Q t' → ∀ u : ∀ PP : Pl D.host.E, (kP PP)ˣ, ∃ s : (AE D)ˣ, ∏ PP ∈ S, ((R.xiR t' PP (u PP) : ℂˣ) : ℂ) = ((R.xi t' s : Circle) : ℂ)) := by
  intro D G _ _ Pl0 T0 A T _ R F hC i t es ϖ n x hes hc hϖ hx
  set Q := R.Q t with hQ

  have hidem : ∀ PP ∈ Q, cA D (es PP) * cA D (es PP) = cA D (es PP) := fun PP hP =>
    Formalism.IndefR.Fin.LevelGroupLemmas.isIdem_cA (hes PP hP).1.1
  have hϖ0 : ∀ PP ∈ Q, star ((ϖ PP : 𝓞 D.host.E) : D.host.E) ≠ 0 := fun PP hP h0 => by
    have : (ϖ PP : D.host.E) = 0 := by rw [← star_star ((ϖ PP : 𝓞 D.host.E) : D.host.E), h0, star_zero]
    exact (hϖ PP hP).2 (by rw [show ϖ PP = 0 from RingOfIntegers.ext this]; exact zero_mem _)
  let y : Q → (AE D)ˣ := fun P =>
    Formalism.L2.JoinChr.locU (hidem P.1 P.2) ((Units.mk0 (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) (hϖ0 P.1 P.2)) ^ n)
  have hyv : ∀ P : Q, ((y P : (AE D)ˣ) : AE D) = 1 + cA D (es P.1) * (incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n - 1) := by
    intro P
    show Formalism.L2.JoinChr.locE D _ _ = _
    unfold Formalism.L2.JoinChr.locE
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, map_pow]
  have horth : ∀ P ∈ Q.attach, ∀ P' ∈ Q.attach, P ≠ P' → cA D (es P.1) * cA D (es P'.1) = 0 := by
    intro P _ P' _ hne
    rw [← map_mul, Formalism.IndefR.Fin.LevelGroupLemmas.idemSum_orth hes rfl hc P.2 P'.2 (fun e => hne (Subtype.ext e)), map_zero]
  have hxy : x = ∏ P ∈ Q.attach, y P := by
    apply Units.ext
    rw [Units.coe_prod, hx]
    simp only [hyv]
    rw [← Finset.sum_attach Q (fun PP => cA D (es PP) * (incA D (star ((ϖ PP : 𝓞 D.host.E) : D.host.E)) ^ n - 1))]
    exact one_add_sum_eq_prod Q.attach (fun P => cA D (es P.1)) (fun P => incA D (star ((ϖ P.1 : 𝓞 D.host.E) : D.host.E)) ^ n) horth

  have hg : ∀ PP ∈ Q, ((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal := fun PP hP =>
    GlobalTheory.StdFrames.g_not_mem (hC.lev.Q_pl t) hP
  have hgc : ∀ PP ∈ Q, ∀ k : Fin 2, ((D.host.g k : ℕ) : 𝓞 D.host.E) ∉ (Formalism.L2.DIV.conjPl PP).asIdeal := by
    intro PP hP k hk
    have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
      have : Formalism.L2.DIV.starOHom ((D.host.g k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := hk
      rwa [map_natCast] at this
    apply hg PP hP
    rw [Nat.cast_mul]
    fin_cases k
    · exact Ideal.mul_mem_right _ _ hk'
    · exact Ideal.mul_mem_left _ _ hk'
  have unrM : ∀ PP ∈ Q, (R.C.mu0 i).UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP hP =>
    (R.C.isMu0 i).unr _ fun k => hgc PP hP k
  have unrE : ∀ PP ∈ Q, R.C.eta.UnrAt (Formalism.L2.DIV.conjPl PP) := fun PP _ => R.C.isEta.unr _

  have hvM : ((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) = ∏ PP ∈ Q, (((R.C.mu0 i).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp (R.mu0 ((i : ℕ) + 1))) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 (hC.lev.mu0 i)
      (unrM P.1 P.2) (hyv P)
  have hvE : ((R.eta x : Circle) : ℂ) = ∏ PP ∈ Q, ((R.C.eta.val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) ^ n := by
    have := map_prod (Circle.coeHom.comp R.eta) y Q.attach
    rw [← hxy] at this
    show (Circle.coeHom.comp R.eta) x = _
    rw [this, ← Finset.prod_attach Q]
    refine Finset.prod_congr rfl fun P _ => ?_
    exact GlobalTheory.T.heckeCharacter_value_at_conjugatePlace_pow D P.1 (es P.1) (ϖ P.1) _ _ n (y P) (hes P.1 P.2) (hϖ P.1 P.2).1 (hϖ P.1 P.2).2 hC.lev.eta
      (unrE P.1 P.2) (hyv P)
  set sq : Pl D.host.E → ℂ := fun PP => ((Real.sqrt (Ideal.absNorm PP.asIdeal : ℝ) : ℝ) : ℂ) with hsq
  set v : Pl D.host.E → ℂ := fun PP => (((R.C.mu0 i * R.C.eta⁻¹).val (Formalism.L2.DIV.conjPl PP) : ℂˣ) : ℂ) with hv
  refine ⟨(((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹, ?_, ?_, ?_⟩
  · intro τ hτ
    have key : (((R.mu0 ((i : ℕ) + 1) x : Circle) : ℂ) * ((R.eta x : Circle) : ℂ)⁻¹)⁻¹ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n =
        ∏ PP ∈ Q, ((v PP * sq PP)⁻¹) ^ n := by
      rw [hvM, hvE]
      simp only [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
      refine Finset.prod_congr rfl fun PP _ => ?_
      simp only [hv, Formalism.L2.Host.HChar.val_mul, Formalism.L2.Host.HChar.val_inv, Units.val_mul, Units.val_inv_eq_inv_val]
      ring
    show τ (_ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n) = _ * ∏ PP ∈ Q, (sq PP)⁻¹ ^ n
    rw [key, map_prod]
    refine Finset.prod_congr rfl fun PP hP => ?_
    rw [map_pow, map_inv₀]
    congr 2
    exact GlobalTheory.T.fixesUntwistedLiftData_conjugatePrime_value_sqrtNorm T R i τ PP hτ (hg PP hP)
  · intro t'
    have h1 := chrW_val R i t' x
    have h2 := chr_inv_val (R.xi t') x
    simp only [h1, h2]
    ring
  · intro t' S hS u
    exact GlobalTheory.FlatConj.prod_val (R.xi t') S (fun PP => ((R.xiR t' PP (u PP) : ℂˣ) : ℂ))
      fun PP hP => GlobalTheory.FlatConj.xiR_val hC t' PP (hS hP) (u PP)
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SphericalWhittakerDiagonalShiftRamifiedCharacter
section
noncomputable section
open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep Formalism.UG GlobalTheory.LFun

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell
variable {k : Type} [Field k] {n : ℕ}

theorem val_tD' (ϖ : kˣ) (a : Fin n → ℤ) : (tD ϖ a).val = Matrix.diagonal fun i => ((ϖ ^ a i : kˣ) : k) :=
  GlobalTheory.SmGL.val_diagT k _

theorem conj_tD_apply (ϖ : kˣ) (c : Fin n → ℤ) (u : GL (Fin n) k) (i j : Fin n) :
    ((tD ϖ c * u * tD ϖ (-c) : GL (Fin n) k) : Matrix (Fin n) (Fin n) k) i j =
      ((ϖ ^ c i : kˣ) : k) * (u : Matrix (Fin n) (Fin n) k) i j * ((ϖ ^ (-c) j : kˣ) : k) := by
  rw [Units.val_mul, Units.val_mul, val_tD', val_tD', Matrix.mul_diagonal, Matrix.diagonal_mul]

theorem tD_eq_diagPow (ϖ : kˣ) (ν : Fin n → ℤ) (h : ∀ i, 0 ≤ ν i) :
    tD ϖ ν = GlobalTheory.JSW.diagPow ϖ (fun i => (ν i).toNat) := by
  have e : (fun i => ((ϖ ^ ν i : kˣ) : k)) = fun i => ((ϖ ^ (ν i).toNat : kˣ) : k) :=
    funext fun i => by rw [← zpow_natCast, Int.toNat_of_nonneg (h i)]
  ext i j
  rw [val_tD', e]
  rfl

theorem commute_tD_const (ϖ : kˣ) (c : ℤ) (x : GL (Fin n) k) : Commute (tD ϖ (fun _ : Fin n => c)) x := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, val_tD']
  ext i j
  rw [Matrix.mul_diagonal, Matrix.diagonal_mul]
  ring

theorem conj_mem_unipB (ϖ : kˣ) (c : Fin n → ℤ) {u : GL (Fin n) k} (hu : u ∈ GlobalTheory.SmGL.unipB k (Fin n)) :
    tD ϖ c * u * tD ϖ (-c) ∈ GlobalTheory.SmGL.unipB k (Fin n) := by
  obtain ⟨h1, h2⟩ := (GlobalTheory.SmGL.mem_unipB k).1 hu
  refine (GlobalTheory.SmGL.mem_unipB k).2 ⟨fun i j hij => ?_, fun i => ?_⟩
  · rw [conj_tD_apply, h1 i j hij, mul_zero, zero_mul]
  · rw [conj_tD_apply, h2 i, mul_one, ← Units.val_mul, Pi.neg_apply, ← _root_.zpow_add, add_neg_cancel, zpow_zero, Units.val_one]

theorem superDiag_conj (ϖ : kˣ) (e : ℤ) (m : ℕ) (u : GL (Fin (m + 1)) k) :
    GlobalTheory.Whittaker.superDiag (tD ϖ (fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))) * u *
      tD ϖ (-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ))))) =
      ((ϖ ^ e : kˣ) : k) * GlobalTheory.Whittaker.superDiag u := by
  rw [GlobalTheory.Whittaker.superDiag, GlobalTheory.Whittaker.superDiag, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun j hj => ?_
  have hj' : (j : ℕ) = (i : ℕ) + 1 := (Finset.mem_filter.1 hj).2
  rw [conj_tD_apply]
  have hz : (ϖ ^ (e * ((m : ℤ) - ((i : ℕ) : ℤ))) : kˣ) * ϖ ^ ((-(fun i : Fin (m + 1) => e * ((m : ℤ) - ((i : ℕ) : ℤ)))) j) = ϖ ^ e := by
    rw [← _root_.zpow_add]
    congr 1
    simp only [Pi.neg_apply, hj']
    push_cast
    ring
  rw [← hz, Units.val_mul]
  ring

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW.ShiftWhit
open GlobalTheory.IwaCell GlobalTheory.JSW GroundTheory.Automorphic GroundTheory.Automorphic.FourierWhittaker GroundTheory.Automorphic.MultiplicityOne GlobalTheory.PRep
variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

def psiScaled (w : HeightOneSpectrum (𝓞 E)) (c : w.adicCompletion E) : AddChar (w.adicCompletion E) ℂ :=
  (psiLocChar w).compAddMonoidHom (AddMonoidHom.mulLeft c)

theorem psiScaled_apply (w : HeightOneSpectrum (𝓞 E)) (c x : w.adicCompletion E) :
    psiScaled w c x = psiLoc w (c * x) := rfl

theorem main_of_fixed (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E))
    (α : Fin (m + 1) → ℂˣ) (hα : HasSatGL w (π.locRep w) (Finset.univ.val.map α))
    (φ : π.V) (hφ : φ ∈ fixed (π.locRep w) (KGL w (m + 1)))
    (ϖ : (w.adicCompletion E)ˣ) (hϖ : IsUnifV E w (ϖ : w.adicCompletion E)) (e : ℤ)
    (hc : GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E))
    (g : GA E (m + 1)) (hg : GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1)
    (ν : Fin (m + 1) → ℤ) (hν : 0 ≤ ν (Fin.last m)) :
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) =
      GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν *
        whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  classical
  set c : Fin (m + 1) → ℤ := fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) with hcdef
  have hsplit : tD ϖ (fun i => c i + ν i) = tD ϖ c * tD ϖ ν := by rw [← tD_add]; rfl
  have hcont : ∀ ψ : π.V, Continuous ψ.1.1 := fun ψ => (π.cusp _ ψ.2).1.continuous
  have hleft : AutomorphicForm.IsLeftInvariant φ.1.1 := fun γ y => by
    rw [show AdelicGLn.diagonal E (m + 1) γ = ratGL E (m + 1) γ from Units.ext (Matrix.ext fun _ _ => rfl)]
    exact (π.cusp _ φ.2).1.left γ y
  let f : π.V →ₗ[ℂ] (GL (Fin (m + 1)) (w.adicCompletion E) → ℂ) :=
    { toFun := fun ψ h => whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
      map_add' := fun ψ ψ' => funext fun h => whit_add (hcont ψ) (hcont ψ') _
      map_smul' := fun c ψ => funext fun h => whit_smul c ψ.1.1 _ }
  have hmul : ∀ h k : GL (Fin (m + 1)) (w.adicCompletion E),
      g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))) =
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) * finGL E (m + 1) (locGL E (m + 1) w k) := by
    intro h k
    rw [← mul_assoc (tD ϖ c) h k, map_mul (locGL E (m + 1) w), map_mul (finGL E (m + 1)), mul_assoc]
  have hf : ∀ k (ψ : π.V), f (π.locRep w k ψ) = rightReg ℂ _ ℂ k (f ψ) := by
    intro k ψ
    funext h
    change whit (fun z => ψ.1.1 (z * finGL E (m + 1) (locGL E (m + 1) w k)))
        (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h))) =
      whit ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k))))
    rw [hmul, whit_mul_right ψ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]

  have hN0 : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h : GL (Fin (m + 1)) (w.adicCompletion E),
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (u * h))) =
        psiLoc w (GlobalTheory.Whittaker.superDiag u) * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w h)) := by
    intro u hu h
    rw [map_mul, map_mul, ← mul_assoc, commute_finGL_locGL w hg u, mul_assoc, finGL_locGL_eq_uGL w hu, whit,
      whittaker_uGL_mul (hcont φ) hleft, supSum_sLoc]
    rfl
  have hN : ∀ u ∈ GlobalTheory.SmGL.unipB (w.adicCompletion E) (Fin (m + 1)), ∀ h,
      f φ (u * h) = psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E)
        (GlobalTheory.Whittaker.superDiag u) * f φ h := by
    intro u hu h
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (u * h)))) =
      _ * whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    have e1 : tD ϖ c * (u * h) = (tD ϖ c * u * tD ϖ (-c)) * (tD ϖ c * h) := by rw [tD_neg]; group
    rw [e1, hN0 _ (conj_mem_unipB ϖ c hu), psiScaled_apply, hcdef, superDiag_conj]
  have hK : ∀ h, ∀ k ∈ KGL w (m + 1), f φ (h * k) = f φ h := by
    intro h k hk
    change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * (h * k)))) =
      whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))
    rw [hmul, whit_mul_right φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * h)))]
    congr 1
    funext z
    exact congrArg (fun ψ : π.V => ψ.1.1 z) (GlobalTheory.LGrp.mem_fixed.1 hφ k hk)
  have hψ : ∀ x : w.adicCompletion E, (∀ y ∈ Ov E w,
      psiScaled w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) (x * y) = 1) ↔ x ∈ Ov E w := by
    intro x
    simp only [psiScaled_apply, ← mul_assoc]
    exact hc x
  have hgoal : f φ (tD ϖ ν) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * f φ 1 := by
    by_cases h0 : φ = 0
    · subst h0
      have hz : ∀ h, f 0 h = 0 := fun h => by rw [map_zero]; rfl
      rw [hz, hz, mul_zero]
    by_cases hanti : Antitone ν
    · have hpos : ∀ i, 0 ≤ ν i := fun i => hν.trans (hanti (Fin.le_last i))
      have hsat := hα.2 φ hφ h0
      have hmain := GlobalTheory.T.shintani_formula_alt E w (m + 1) _ hψ (f φ) α hN hK ?_ ϖ hϖ (fun i => (ν i).toNat)
      · rw [GlobalTheory.RSCell.sphZ, if_pos hanti, tD_eq_diagPow ϖ ν hpos]
        exact hmain
      · intro ϖ' hϖ' j hj
        rw [← map_heckeVec (Final.GLintComm E w (m + 1)) (Tj_mem_hecke hϖ' j) f hf, hsat.2.2.2 ϖ' hϖ' j hj, map_smul]
    · rw [GlobalTheory.RSCell.sphZ, if_neg hanti, zero_mul]
      set M : ℕ := ∑ i, (ν i).natAbs
      have hM : ∀ i, (ν i).natAbs ≤ M := fun i =>
        Finset.single_le_sum (f := fun i => (ν i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
      set ν' : Fin (m + 1) → ℤ := fun i => ν i + M
      have hpos : ∀ i, 0 ≤ ν' i := fun i => by have := hM i; simp only [ν']; omega
      set z := tD ϖ (fun _ : Fin (m + 1) => -(M : ℤ))
      have hνz : tD ϖ ν = tD ϖ ν' * z := by
        rw [← tD_add]; congr 1; funext i; simp only [ν', Pi.add_apply]; ring
      have hanti' : ¬ Antitone (fun i => (ν' i).toNat) := by
        intro ha
        refine hanti fun i j hij => ?_
        have := ha hij
        have h1 := Int.toNat_of_nonneg (hpos i)
        have h2 := Int.toNat_of_nonneg (hpos j)
        simp only [ν'] at this h1 h2
        omega
      have hz := GlobalTheory.T.whittaker_diagonal_eq_zero_of_not_antitone E w (m + 1) _ hψ (fun h => f φ (h * z))
        (fun u hu h => by simp only [mul_assoc]; exact hN u hu (h * z))
        (fun h k hk => by
          show f φ (h * k * z) = f φ (h * z)
          rw [mul_assoc, ← (commute_tD_const ϖ _ k).eq, ← mul_assoc, hK _ k hk])
        ϖ hϖ (fun i => (ν' i).toNat) hanti'
      rw [hνz, tD_eq_diagPow ϖ ν' hpos]
      exact hz
  have e2 := hgoal
  change whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * tD ϖ ν))) = _ *
    whit φ.1.1 (g * finGL E (m + 1) (locGL E (m + 1) w (tD ϖ c * 1))) at e2
  rw [mul_one, ← hsplit] at e2
  exact e2

end GlobalTheory.JSW.ShiftWhit

namespace GlobalTheory.JSW

theorem whit_mul_locGL_tD_shift : ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (m : ℕ) (π : CuspSub E (m + 1)) (w : HeightOneSpectrum (𝓞 E)) (α : Fin (m + 1) → ℂˣ), HasSatGL w (π.locRep w) (Finset.univ.val.map α) → ∀ φ ∈ π.V, (∀ k ∈ KGL w (m + 1), act (.fin (locGL E (m + 1) w k)) φ = φ) → ∀ (ϖ : (w.adicCompletion E)ˣ), IsUnifV E w (ϖ : w.adicCompletion E) → ∀ e : ℤ, GlobalTheory.RamShift.CondOne w ((ϖ ^ e : (w.adicCompletion E)ˣ) : w.adicCompletion E) → ∀ g : GA E (m + 1), GeneralLinearGroup.map ((pLoc E w).comp (pFin E)) g = 1 → ∀ ν : Fin (m + 1) → ℤ, 0 ≤ ν (Fin.last m) → GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)) + ν i)))) = GlobalTheory.RSCell.sphZ (qV E w) (fun i => (α i : ℂ)) ν * GlobalTheory.JSW.whit φ.1 (g * finGL E (m + 1) (locGL E (m + 1) w (GlobalTheory.IwaCell.tD ϖ (fun i => e * ((m : ℤ) - ((i : ℕ) : ℤ)))))) := by
  intro E _ _ _ m π w α hα φ hφV hφ ϖ hϖ e hc g hg ν hν
  exact GlobalTheory.JSW.ShiftWhit.main_of_fixed m π w α hα ⟨φ, hφV⟩
    (GlobalTheory.LGrp.mem_fixed.2 fun k hk => Subtype.ext (hφ k hk)) ϖ hϖ e hc g hg ν hν

end GlobalTheory.JSW
end
end

-- bundled from Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TwistedPlaceSelmerLengthBoundOfLocalDuality
section
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions Formalism.MainNotions.N Formalism.WeaklyAdmissibleFiltrations Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain

namespace GlobalTheory.TwistedPlaceBound

theorem closing : GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.BlochKatoLocal → Formalism.GaloisCohomology.LocalTateDualityK → Formalism.GaloisCohomology.LocalEulerCharK → ∀ (D : D7) (HW : HWOf D.loc) (F : FonOf D.loc D.locA HW) (Cm : CmpOf D.loc D.locA HW F), ∀ (r : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.nV) (D.nd.O i))) (ρ : ∀ i : D.nd.Loc, D.nd.X i → (GE D.nd →* GL (Fin D.R.r) (D.nd.O i))) (large₂ : SizeData₂ D) (ep : Bool) (C : ℝ) (Qp : MvPolynomial (Fin 3) ℕ), 2080 ≤ C → (∀ f r t : ℕ, 260 * f ^ 2 * t ^ 2 * (r + t) ≤ EmbeddingTypeJumps.polyVal Qp f r t) → EmbeddingTypeJumps.GlobalIndexAwayFromTypes r ρ → EmbeddingTypeJumps.admG1 r → EmbeddingTypeJumps.admG2 r ρ → EmbeddingTypeJumps.admG3 r ρ → EmbeddingTypeJumps.admG4 r → EmbeddingTypeJumps.admG5 r → EmbeddingTypeJumps.admG6 r → EmbeddingTypeJumps.iwahoriAdmissibleSet r ρ → EmbeddingTypeJumps.KillingTwistedPlaces ρ → EmbeddingTypeJumps.HodgeJumpWindowsAtDistinguishedPrimes r ep large₂ → EmbeddingTypeJumps.FontaineSubOfSumsAtDistinguishedPrimes r ρ → (∀ i : D.nd.Loc, EmbeddingTypeJumps.AtQD i → TruncatedSeriesCountingIdentities.TameGeneratorConditions i) → EmbeddingTypeJumps.ParametersPolynomiallyBounded large₂ → EmbeddingTypeJumps.Conclusion0 D ∧ EmbeddingTypeJumps.Conclusion1 D ∧ EmbeddingTypeJumps.Conclusion2 ρ large₂ C Qp := by
  intro hGAR hBKL hLTD hLEC D HW F Cm r ρ large₂ ep C Qp hC hQ hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hKill hJump hFon hG5x hPar
  have hUsed := GlobalTheory.T.wachModuleLocalConclusions_usedForms D HW F Cm
  have hW : EmbeddingTypeJumps.admW (D := D) HW F := by
    intro i _ w hw Cf h
    exact GlobalTheory.T.wachHypothesis_crystallineLattices D HW F Cm hUsed.1 hUsed.2 (GlobalTheory.crysOnCond_all D HW F) (D.nd.l i) _ 1 Cf.LL h
  have hA : EmbeddingTypeJumps.admA (D := D) 160 := GlobalTheory.T.localLifting_of_blochKato_tateDuality_eulerChar hBKL hLTD hLEC D HW F Cm 160 le_rfl
  have hTB : EmbeddingTypeJumps.admTB (D := D) HW F := GlobalTheory.T.theorem_tb_of_local_blochKato_duality_euler hBKL hLTD hLEC D HW F Cm
  have hBK : EmbeddingTypeJumps.admBK (D := D) := GlobalTheory.T.blochKatoLocal_all_of_tateDuality_eulerChar hBKL hLTD hLEC D
  have hLit : EmbeddingTypeJumps.LiteratureHypotheses (D := D) := by
    intro i hi
    refine ⟨hG5x i hi, fun w hw Cf => ⟨?_, GlobalTheory.T.blochKatoDim_at_auxiliary_prime_places hLTD hLEC D i hi w hw Cf⟩,
      GlobalTheory.BridgeTie.localCoefficientCompatibility D i, GlobalTheory.FontaineAdm.fontaineProperties_all_places D i, GlobalTheory.T.integral_tate_H2_top hLTD D i,
      GlobalTheory.T.unramifiedClassFieldBound_of_artin hGAR D i⟩
    exact Formalism.MainNotions.TruncatedSeriesCountingIdentities.tate_duality_h2_of_all_coefficients _ _ _
      (GlobalTheory.TateTop.tateH2_of_duality_loc hLTD (D.nd.l i) (D.loc (D.nd.l i)) (D.nbr i w hw).Kw)
      (GlobalTheory.HTW.Rec.goodO_finExt_integers (D.nd.l i) Cf.LL)
  have h01 := GlobalTheory.T.local_fields_at_auxiliary_primes D
  refine ⟨h01.1, h01.2, ?_⟩
  exact GlobalTheory.T.theoremB_of_admittedHypotheses D HW F r ρ large₂ ep 160 C Qp (by rw [max_eq_left (by norm_num)]; linarith) hQ hW hA
    hN5 hG1 hG2 hG3 hG4 hG5 hG6 hSet hTB hBK hKill hJump hFon hLit hPar

end GlobalTheory.TwistedPlaceBound
end

